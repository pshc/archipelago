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
#include <llvm/Support/CallSite.h>

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
  /// from a function so that "finally"-style code can be inserted. In addition
  /// to finding the existing return and unwind instructions, it also (if
  /// necessary) transforms any call instructions into invokes and sends them to
  /// a landing pad.
  ///
  /// It's wrapped up in a state machine using the same transform C# uses for
  /// 'yield return' enumerators, This transform allows it to be non-allocating.
  class EscapeEnumerator {
    Function &F;
    const char *CleanupBBName;

    // State.
    int State;
    Function::iterator StateBB, StateE;
    IRBuilder<> Builder;

  public:
    EscapeEnumerator(Function &F, const char *N = "cleanup")
      : F(F), CleanupBBName(N), State(0), Builder(F.getContext()) {}

    IRBuilder<> *Next() {
      switch (State) {
      default:
        return 0;

      case 0:
        StateBB = F.begin();
        StateE = F.end();
        State = 1;

      case 1:
        // Find all 'return', 'resume', and 'unwind' instructions.
        while (StateBB != StateE) {
          BasicBlock *CurBB = StateBB++;

          // Branches and invokes do not escape, only unwind, resume, and return
          // do.
          TerminatorInst *TI = CurBB->getTerminator();
          if (!isa<ReturnInst>(TI) && !isa<ResumeInst>(TI))
            continue;

          Builder.SetInsertPoint(TI->getParent(), TI);
          return &Builder;
        }

        State = 2;

        // Find all 'call' instructions.
        SmallVector<Instruction*,16> Calls;
        for (Function::iterator BB = F.begin(),
                                E = F.end(); BB != E; ++BB)
          for (BasicBlock::iterator II = BB->begin(),
                                    EE = BB->end(); II != EE; ++II)
            if (CallInst *CI = dyn_cast<CallInst>(II))
              if (!CI->getCalledFunction() ||
                  !CI->getCalledFunction()->getIntrinsicID())
                Calls.push_back(CI);

        if (Calls.empty())
          return 0;

        // Create a cleanup block.
        LLVMContext &C = F.getContext();
        BasicBlock *CleanupBB = BasicBlock::Create(C, CleanupBBName, &F);
        Type *ExnTy = StructType::get(Type::getInt8PtrTy(C),
                                      Type::getInt32Ty(C), NULL);
        Constant *PersFn =
          F.getParent()->
          getOrInsertFunction("__gcc_personality_v0",
                              FunctionType::get(Type::getInt32Ty(C), true));
        LandingPadInst *LPad = LandingPadInst::Create(ExnTy, PersFn, 1,
                                                      "cleanup.lpad",
                                                      CleanupBB);
        LPad->setCleanup(true);
        ResumeInst *RI = ResumeInst::Create(LPad, CleanupBB);

        // Transform the 'call' instructions into 'invoke's branching to the
        // cleanup block. Go in reverse order to make prettier BB names.
        SmallVector<Value*,16> Args;
        for (unsigned I = Calls.size(); I != 0; ) {
          CallInst *CI = cast<CallInst>(Calls[--I]);

          // Split the basic block containing the function call.
          BasicBlock *CallBB = CI->getParent();
          BasicBlock *NewBB =
            CallBB->splitBasicBlock(CI, CallBB->getName() + ".cont");

          // Remove the unconditional branch inserted at the end of CallBB.
          CallBB->getInstList().pop_back();
          NewBB->getInstList().remove(CI);

          // Create a new invoke instruction.
          Args.clear();
          CallSite CS(CI);
          Args.append(CS.arg_begin(), CS.arg_end());

          InvokeInst *II = InvokeInst::Create(CI->getCalledValue(),
                                              NewBB, CleanupBB,
                                              Args, CI->getName(), CallBB);
          II->setCallingConv(CI->getCallingConv());
          II->setAttributes(CI->getAttributes());
          CI->replaceAllUsesWith(II);
          delete CI;
        }

        Builder.SetInsertPoint(RI->getParent(), RI);
        return &Builder;
      }
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

    // Push the new frame map onto the global linked list.
    Constant *numRootsConst = ConstantInt::get(Type::getInt32Ty(Context),
                                               numRoots, false);
    Instruction *prevFramePtr  = CreateGEP(Context, AtEntry,
                                           StackEntry,0,0,"gc_frame.prev");
    Instruction *numRootsPtr   = CreateGEP(Context, AtEntry,
                                           StackEntry,0,1,"gc_frame.numroots");
    Instruction *newGlobalRoot = CreateGEP(Context, AtEntry,
                                           StackEntry, 0, "gc_thisframe");
    AtEntry.CreateStore(prevFrame, prevFramePtr);
    AtEntry.CreateStore(numRootsConst, numRootsPtr);
    AtEntry.CreateStore(newGlobalRoot, globalRoot);
  }

  // For each instruction that escapes...
  EscapeEnumerator EE(F, "gc_cleanup");
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
