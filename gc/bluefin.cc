//===----------------------------------------------------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements lowering for the llvm.gc* intrinsics for targets that do
// not natively support them (which includes the C backend). Note that the code
// generated is not quite as efficient as algorithms which generate stack maps
// to identify roots.
//
// This pass implements the code transformation described in this paper:
//   "Accurate Garbage Collection in an Uncooperative Environment"
//   Fergus Henderson, ISMM, 2002
//
// In order to support this particular transformation, all stack roots are
// coallocated in the stack. This allows a fully target-independent stack map
// while introducing only minor runtime overhead.
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "bluefin"

#include <llvm/CodeGen/GCStrategy.h>
#include <llvm/IRBuilder.h>
#include <llvm/IntrinsicInst.h>
#include <llvm/Module.h>

using namespace llvm;

typedef std::vector<std::pair<CallInst*, AllocaInst*> > roots_t;

namespace {

class LLVM_LIBRARY_VISIBILITY Bluefin : public GCStrategy {
public:
  Bluefin();
  virtual ~Bluefin();
  virtual bool initializeCustomLowering(Module &M);
  virtual bool performCustomLowering(Function &F);

private:
  GlobalVariable *globalRoot;
  StructType *stackMapHeaderTy;
};

}

namespace {
  /// EscapeEnumerator - This is a little algorithm to find all escape points
  /// from a function so that "finally"-style code can be inserted.
  class EscapeEnumerator {
    Function::iterator StateBB, StateE;
    IRBuilder<> Builder;

  public:
    EscapeEnumerator(Function &F)
      : StateBB(F.begin()), StateE(F.end()), Builder(F.getContext()) {}

    IRBuilder<> *Next() {
      // Find all 'return', 'resume', and 'unwind' instructions.
      while (StateBB != StateE) {
        BasicBlock *CurBB = StateBB++;

        // Branches and invokes do not escape,
        // only unwind, resume, and return do.
        TerminatorInst *TI = CurBB->getTerminator();
        assert(!isa<ResumeInst>(TI) && "exceptions not supported");
        if (!isa<ReturnInst>(TI))
          continue;

        Builder.SetInsertPoint(TI->getParent(), TI);
        return &Builder;
      }
      return 0;
    }
  };
}

// -----------------------------------------------------------------------------

Bluefin::Bluefin() {
  globalRoot = NULL;
  stackMapHeaderTy = NULL;

  CustomRoots = true;
}

Bluefin::~Bluefin() { }

bool Bluefin::initializeCustomLowering(Module &M) {
  LLVMContext &Context = M.getContext();

  // Set up stack map common header type.
  stackMapHeaderTy = StructType::create(Context, "gc_stackentry");
  std::vector<Type*> EltTys;
  EltTys.push_back(PointerType::getUnqual(stackMapHeaderTy)); // *prev frame
  EltTys.push_back(Type::getInt8PtrTy(Context)); // func name
  EltTys.push_back(Type::getInt32Ty(Context)); // num roots
  stackMapHeaderTy->setBody(EltTys);

  // Initialize global stack map linked list.
  PointerType *stackMapPtrTy = PointerType::getUnqual(stackMapHeaderTy);

  globalRoot = M.getGlobalVariable("bluefin_root");
  if (!globalRoot) {
    globalRoot = new GlobalVariable(M, stackMapPtrTy, false,
                                    GlobalValue::LinkOnceAnyLinkage,
                                    Constant::getNullValue(stackMapPtrTy),
                                    "bluefin_root");
  }
  else if (globalRoot->hasExternalLinkage() && globalRoot->isDeclaration()) {
    globalRoot->setInitializer(Constant::getNullValue(stackMapPtrTy));
    globalRoot->setLinkage(GlobalValue::LinkOnceAnyLinkage);
  }

  return true;
}

static void collectGcRoots(Function &F, roots_t &funcGcRoots) {
  // FIXME: Account for original alignment. Could fragment the root array.
  //   Approach 1: Null initialize empty slots at runtime. Yuck.
  //   Approach 2: Emit a map of the array instead of just a count.

  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB)
    for (BasicBlock::iterator II = BB->begin(), E = BB->end(); II != E;)
      if (IntrinsicInst *CI = dyn_cast<IntrinsicInst>(II++))
        if (Function *F = CI->getCalledFunction())
          if (F->getIntrinsicID() == Intrinsic::gcroot) {

            std::pair<CallInst*, AllocaInst*> Pair = std::make_pair(
              CI, cast<AllocaInst>(CI->getArgOperand(0)->stripPointerCasts()));

            //assert(isNull(CI->getArgOperand(1)) && "Unexpected metadata");

            funcGcRoots.push_back(Pair);
          }
}

static GetElementPtrInst *
CreateGEP(LLVMContext &Context, IRBuilder<> &B, Value *BasePtr,
                         int Idx, int Idx2, const char *Name) {
  Value *Indices[] = { ConstantInt::get(Type::getInt32Ty(Context), 0),
                       ConstantInt::get(Type::getInt32Ty(Context), Idx),
                       ConstantInt::get(Type::getInt32Ty(Context), Idx2) };
  Value* Val = B.CreateGEP(BasePtr, Indices, Name);

  assert(isa<GetElementPtrInst>(Val) && "Unexpected folded constant");

  return dyn_cast<GetElementPtrInst>(Val);
}

static GetElementPtrInst *
CreateGEP(LLVMContext &Context, IRBuilder<> &B, Value *BasePtr,
                         int Idx, const char *Name) {
  Value *Indices[] = { ConstantInt::get(Type::getInt32Ty(Context), 0),
                       ConstantInt::get(Type::getInt32Ty(Context), Idx) };
  Value *Val = B.CreateGEP(BasePtr, Indices, Name);

  assert(isa<GetElementPtrInst>(Val) && "Unexpected folded constant");

  return dyn_cast<GetElementPtrInst>(Val);
}

bool Bluefin::performCustomLowering(Function &F) {
  roots_t funcGcRoots;
  collectGcRoots(F, funcGcRoots);
  const size_t numRoots = funcGcRoots.size();
  if (numRoots == 0)
    return false;

  LLVMContext &Context = F.getContext();

  // Function start.
  BasicBlock::iterator IP = F.getEntryBlock().begin();
  IRBuilder<> AtEntry(IP->getParent(), IP);

  // Allocate stack map.
  Instruction *StackEntry;
  {
    std::vector<Type*> EltTys;
    EltTys.push_back(stackMapHeaderTy);
    for (size_t i = 0; i < numRoots; i++)
      EltTys.push_back(funcGcRoots[i].second->getAllocatedType());

    Type *ty = StructType::create(EltTys, "gc_stackentry."+F.getName().str());
    StackEntry = AtEntry.CreateAlloca(ty, 0, "gc_frame");
  }

  // After all the allocas...
  while (isa<AllocaInst>(IP)) ++IP;
  AtEntry.SetInsertPoint(IP->getParent(), IP);


  {
    // Load the current gc frame pointer (to the caller's frame).
    Instruction *prevFrame = AtEntry.CreateLoad(globalRoot, "gc_prevframe");

    for (size_t i = 0; i < numRoots; i++) {
      // For each root, find the corresponding slot in the aggregate...
      // (first slot is the {prev, numroots} struct)
      Value *slot = CreateGEP(Context, AtEntry, StackEntry, i+1, "gc_root");

      // And use it in lieu of the alloca.
      AllocaInst *OriginalAlloca = funcGcRoots[i].second;
      slot->takeName(OriginalAlloca);
      OriginalAlloca->replaceAllUsesWith(slot);
    }

    // Move past the original NULL writes inserted by GCStrategy::InitRoots.
    while (isa<StoreInst>(IP)) ++IP;
    AtEntry.SetInsertPoint(IP->getParent(), IP);

    // XXX: Breaks function pass contract, but should be safe
    Value *funcNameStr = AtEntry.CreateGlobalStringPtr(F.getName().str(),
                         "func_name");

    // Push the new frame map onto the global linked list.
    Constant *numRootsConst = ConstantInt::get(Type::getInt32Ty(Context),
                                               numRoots, false);
    Instruction *prevFramePtr  = CreateGEP(Context, AtEntry,
                                           StackEntry,0,0,"gc_frame.prev");
    Instruction *funcNamePtr   = CreateGEP(Context, AtEntry,
                                           StackEntry,0,1,"gc_frame.name");
    Instruction *numRootsPtr   = CreateGEP(Context, AtEntry,
                                           StackEntry,0,2,"gc_frame.numroots");
    Instruction *newGlobalRoot = CreateGEP(Context, AtEntry,
                                           StackEntry, 0, "gc_thisframe");
    AtEntry.CreateStore(prevFrame, prevFramePtr);
    AtEntry.CreateStore(funcNameStr, funcNamePtr);
    AtEntry.CreateStore(numRootsConst, numRootsPtr);
    AtEntry.CreateStore(newGlobalRoot, globalRoot);
  }

  // For each instruction that escapes...
  EscapeEnumerator EE(F);
  while (IRBuilder<> *AtExit = EE.Next()) {
    // Pop the entry from the shadow stack. Don't reuse prevFrame from
    // AtEntry, since that would make the value live for the entire function.
    Instruction *prevFrame = CreateGEP(Context, *AtExit, StackEntry, 0, 0,
                                           "gc_frame.prev");
    Value *origGlobalRoot = AtExit->CreateLoad(prevFrame, "gc_prevframe");
    AtExit->CreateStore(origGlobalRoot, globalRoot);
  }

  // Delete the original allocas (which are no longer used) and the intrinsic
  // calls (which are no longer valid). Doing this last avoids invalidating
  // iterators.
  for (size_t i = 0; i < numRoots; i++) {
    funcGcRoots[i].first->eraseFromParent();
    funcGcRoots[i].second->eraseFromParent();
  }

  return true;
}

static GCRegistry::Add<Bluefin>
  X("bluefin", "Archipelago Garbage Collector");
