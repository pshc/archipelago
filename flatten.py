from base import *
from atom import *
from quilt import *
import vat

ControlFlowState = DT('ControlFlowState',
        ('block', 'Maybe(Block)'),
        ('level', int),
        ('pendingExits', {int: ['*Block']}),
        ('gcVars', ['*Var']),
        ('scopeVars', ['*Var']),
        ('pastBlocks', [Block]))

CFG = new_env('CFG', ControlFlowState)

LoopInfo = DT('LoopInfo', ('level', int), ('entryBlock', '*Block'))

LOOP = new_env('LOOP', LoopInfo)

PatMatchInfo = DT('PatMatchInfo', ('failProof', bool), ('failBlock', '*Block'))

PATMATCH = new_env('PATMATCH', PatMatchInfo)

NEWFUNCS = new_env('NEWFUNCS', [BlockFunc])

def initial_cfg_state():
    return ControlFlowState(Just(empty_block('', 0)), 0, {}, [], [], [])

def empty_block(label, index):
    label = '%s.%d' % (label, index)
    return Block(label, [], [], TermInvalid(), [])

def start_new_block(label, index):
    "Closes up the current block if any, then returns a fresh one."
    new = empty_block(label, index)
    cfg = env(CFG)
    m = match(cfg.block)
    if m('Just(block)'):
        old = m.block
        jumps(old, new)
        cfg.pastBlocks.append(old)
    cfg.block = Just(new)
    resolve_pending_exits(new)
    return new

def block_push(stmt):
    m = match(env(CFG).block)
    if m('Just(block)'):
        m.block.stmts.append(stmt)

def jumps(src, dest):
    assert matches(src.terminator, 'TermInvalid()'), \
            "Block %s's terminator already resolved?!" % (src,)
    src.terminator = TermJump(dest)
    dest.entryBlocks.append(src)

def resolve_pending_exits(destBlock):
    cfg = env(CFG)
    level = cfg.level
    if level not in cfg.pendingExits:
        return
    pending = cfg.pendingExits[level]
    del cfg.pendingExits[level]
    for block in pending:

        # dumb hack
        m = match(block.terminator)
        if m('TermJumpCond(_, t, f)'):
            if m.t is None:
                assert m.f is not None
                block.terminator.trueDest = destBlock
                destBlock.entryBlocks.append(block)
            elif m.f is None:
                block.terminator.falseDest = destBlock
                destBlock.entryBlocks.append(block)
            else:
                assert False
            continue

        jumps(block, destBlock)

def is_gc_var(var):
    t = extrinsic(TypeOf, var)
    return is_strong_type(t) and not matches(t, "TFunc(_, _, _)") # todo

def null_out_scope_vars():
    cfg = env(CFG)
    if isJust(cfg.block):
        nullOuts = fromJust(cfg.block).nullOuts
        for var in cfg.scopeVars:
            if is_gc_var(var):
                nullOuts.append(var)
    cfg.scopeVars = []

def finish_block(term):
    "Closes up the current block with a terminator."
    cfg = env(CFG)
    if isNothing(cfg.block):
        return
    finished = fromJust(cfg.block)
    assert matches(finished.terminator, 'TermInvalid()')
    finished.terminator = term
    cfg.pastBlocks.append(finished)
    cfg.block = Nothing()

def finish_jump(block):
    "Finishes with TermJump and also updates entryBlock on the dest block."
    cfg = env(CFG)
    if isNothing(cfg.block):
        return
    block.entryBlocks.append(fromJust(cfg.block))
    finish_block(TermJump(block))

def exit_to_level(level):
    "Terminates current block, later resolving to the next block at level."
    cfg = env(CFG)
    if isNothing(cfg.block):
        return
    curLevel = cfg.level
    assert level <= curLevel, "Bad exit to inner level"
    block = fromJust(cfg.block)
    cfg.pendingExits.setdefault(level, []).append(block)
    cfg.block = Nothing()
    cfg.pastBlocks.append(block)

def build_body_and_exit_to_level(body, exitLevel):
    # exit_to_level really ought to occur while inside body
    vat.visit(ControlFlowBuilder, body, 'Body(LExpr)')
    exit_to_level(exitLevel)

def orig_index(stmt):
    return vat.orig_loc(stmt).index

class ControlFlowBuilder(vat.Visitor):
    def TopFunc(self, top):
        state = initial_cfg_state()
        in_env(CFG, state, lambda: self.visit('func'))
        assert state.level == 0
        assert 0 not in state.pendingExits
        blocks = state.pastBlocks
        if isJust(state.block):
            last = fromJust(state.block)
            last.terminator = TermReturnNothing()
            blocks.append(last)
        elif len(blocks) == 0:
            b = empty_block('', 0)
            b.terminator = TermReturnNothing()
            blocks.append(b)
        params = map(LVar, top.func.params)
        # params might need to also be in gcVars?
        bf = BlockFunc(top.var, state.gcVars, params, blocks)
        env(NEWFUNCS).append(bf)

    def FuncExpr(self, fe):
        assert False, "FuncExprs ought to be gone"

    def Body(self, body):
        cfg = env(CFG)
        outerLevel = cfg.level
        innerLevel = outerLevel + 1
        outerDefns = cfg.scopeVars

        cfg.level = innerLevel
        cfg.scopeVars = []

        self.visit()
        assert innerLevel not in cfg.pendingExits, "Dangling exit?"
        # this assumes that finish() is going to get called soon,
        # which is safe enough for now, but really fragile
        null_out_scope_vars()

        cfg.scopeVars = outerDefns
        cfg.level = outerLevel

    def Break(self, stmt):
        null_out_scope_vars()
        exit_to_level(env(LOOP).level)

    def NextCase(self, stmt):
        cfg = env(CFG)
        curBlock = fromJust(cfg.block)
        pm = env(PATMATCH)
        pm.failProof = False
        pm.failBlock.entryBlocks.append(curBlock)
        successBlock = empty_block('patok', orig_index(stmt))
        successBlock.entryBlocks.append(curBlock)

        #null_out_scope_vars()
        finish_block(TermJumpCond(stmt.test, pm.failBlock, successBlock))
        env(CFG).block = Just(successBlock)

    def BlockCond(self, cond):
        cfg = env(CFG)
        exitLevel = cfg.level
        n = len(cond.cases)

        for i in xrange(n-1):
            case = cond.cases[i]
            assert isJust(cfg.block), "Unreachable case %s?" % (case,)

            nextTest = empty_block('matchcase', orig_index(cond.cases[i+1]))

            info = PatMatchInfo(True, nextTest)
            in_env(PATMATCH, info, lambda:
                    vat.visit(ControlFlowBuilder, case.test, 'Body(LExpr)'))
            assert not info.failProof
            build_body_and_exit_to_level(case.body, exitLevel)
            cfg.block = Just(nextTest)

        # last case
        case = cond.cases[n-1]
        assert isJust(cfg.block), "Unreachable case %s?" % (case,)
        info = PatMatchInfo(True, None)
        in_env(PATMATCH, info, lambda:
                vat.visit(ControlFlowBuilder, case.test, 'Body(LExpr)'))
        assert info.failProof
        build_body_and_exit_to_level(case.body, exitLevel)

        if exitLevel in cfg.pendingExits:
            _ = start_new_block('endmatch', orig_index(cond))

    def Cond(self, cond):
        cfg = env(CFG)
        exitLevel = cfg.level
        n = len(cond.cases)
        for i, case in enumerate(cond.cases):
            assert isJust(cfg.block), "Unreachable case?"

            if matches(case.test, "Bind(key('True'))"):
                # makeshift else
                block = fromJust(cfg.block)
                if block.label[:4] == 'elif':
                    block.label = 'else' + block.label[4:]
                build_body_and_exit_to_level(case.body, exitLevel)
                continue

            isLast = (i == n-1)
            true = empty_block('then', orig_index(case))

            # XXX type hack
            nextTest = None if isLast else \
                    empty_block('elif', orig_index(cond.cases[i+1]))

            test, converse = elide_NOTs(case.test)
            jump = TermJumpCond(test, nextTest, true) if converse else \
                    TermJumpCond(test, true, nextTest)
            curBlock = fromJust(cfg.block)
            true.entryBlocks.append(curBlock)
            if isLast:
                # resolve the conditional fall-through later (hack)
                pends = cfg.pendingExits.setdefault(exitLevel, [])
                pends.append(curBlock)
            else:
                nextTest.entryBlocks.append(curBlock)
            finish_block(jump)
            cfg.block = Just(true)
            build_body_and_exit_to_level(case.body, exitLevel)
            if not isLast:
                cfg.block = Just(nextTest)

        if exitLevel in cfg.pendingExits:
            _ = start_new_block('endif', orig_index(cond))

    def Continue(self, stmt):
        null_out_scope_vars()
        finish_jump(env(LOOP).entryBlock)

    def Return(self, stmt):
        env(CFG).scopeVars = []
        finish_block(TermReturn(stmt.expr))

    def ReturnNothing(self, stmt):
        env(CFG).scopeVars = []
        finish_block(TermReturnNothing())

    def While(self, stmt):
        cfg = env(CFG)
        exitLevel = cfg.level
        start = start_new_block('while', orig_index(stmt))
        body = start_new_block('whilebody', orig_index(stmt))
        def go():
            self.visit('body')
            finish_jump(start)
        in_env(LOOP, LoopInfo(exitLevel, start), go)

        if matches(stmt.test, 'key("True")'):
            # maybe infinite loop; don't put the TermJumpCond in
            if exitLevel in cfg.pendingExits:
                # there was a break somewhere, so resolve it to here
                _ = start_new_block('endwhile', orig_index(stmt))
        else:
            end = start_new_block('endwhile', orig_index(stmt))
            start.terminator = TermJumpCond(stmt.test, body, end)
            # body.entryBlocks is already set up (already contains start)
            end.entryBlocks.append(start)

    def Assign(self, assign):
        block_push(assign)
    def AugAssign(self, assign):
        block_push(assign)
    def Defn(self, stmt):
        block_push(stmt)
        self.visit('pat')
    def VoidStmt(self, stmt):
        block_push(stmt)
        m = match(stmt.voidExpr)
        if m('VoidCall(Bind(f), _)'):
            if matches(extrinsic(TypeOf, m.f), 'TFunc(_, Bottom(), _)'):
                null_out_scope_vars()
                finish_block(TermUnreachable())
    # ugh what is this doing here
    def WriteExtrinsic(self, stmt):
        block_push(stmt)

    def t_Stmt(self, stmt):
        assert False, "Can't deal with %s" % stmt

    def Var(self, var):
        cfg = env(CFG)
        cfg.scopeVars.append(var)
        if is_gc_var(var):
            cfg.gcVars.append(var)

def elide_NOTs(test):
    "Optimizes out trivial NOTs."
    converse = False
    m = match(test)
    if m('Call(Bind(key("not")), [con])'):
        m2 = match(m.con)
        if m2('Call(Bind(key("not")), [concon])'):
            return m2.concon, False
        else:
            return m.con, True
    else:
        return test, False

def check_cfg_func(func):
    assert len(func.blocks) > 0
    entryCounts = {}
    for src in func.blocks:
        m = match(src.terminator)
        if m('TermJump(dest)'):
            assert src in m.dest.entryBlocks
            entryCounts[m.dest] = entryCounts.get(m.dest, 0) + 1
        elif m('TermJumpCond(_, d1, d2)'):
            assert src in m.d1.entryBlocks
            entryCounts[m.d1] = entryCounts.get(m.d1, 0) + 1
            assert src in m.d2.entryBlocks
            entryCounts[m.d2] = entryCounts.get(m.d2, 0) + 1
        elif m('TermReturn(_) or TermReturnNothing() or TermUnreachable()'):
            pass
        else:
            assert False, "Found %s" % (src.terminator,)
    # check that all entry blocks are accounted for
    first = True
    for block in func.blocks:
        n = len(block.entryBlocks)
        lbl = block.label
        if first:
            first = False
        else:
            assert n > 0, "Block %s has no entry" % (lbl,)
        if n > 0:
            assert block in entryCounts, "Block %s never sees a jump" % (lbl,)
            assert entryCounts[block] == n, \
                    "Saw %d jumps to %s, but it specifies %d entryBlocks!" % (
                    entryCounts[block], lbl, n,)

def build_control_flow(unit):
    funcs = []
    t = t_DT(ExpandedUnit)
    in_env(NEWFUNCS, funcs, lambda: vat.visit(ControlFlowBuilder, unit, t))

    if env(GENOPTS).dumpBlocks:
        for func in funcs:
            print 'FUNC', extrinsic(Name, func.var)
            for block in func.blocks:
                if block.entryBlocks:
                    print fmtcol('{0}: ^LG; entry from {1}^N', block.label,
                            ', '.join(b.label for b in block.entryBlocks))
                for stmt in block.stmts:
                    print '   ', stmt
                print '   ', match(block.terminator,
                    ('TermJump(d)', lambda d: 'j %s' % (d.label,)),
                    ('TermJumpCond(c, t, f)', lambda c, t, f:
                        'j %r, %s, %s' % (c, t.label, f.label)),
                    ('TermReturnNothing()', lambda: 'ret void'),
                    ('TermReturn(e)', lambda e: 'ret %r' % (e,)),
                    ('TermUnreachable()', lambda: 'unreachable'))
            print

    map_(check_cfg_func, funcs)
    return BlockUnit(funcs)

NEWBODY = new_env('NEWBODY', Body)

def push_newbody(s):
    env(NEWBODY).stmts.append(s)

class CompoundFlattener(vat.Mutator):
    def Body(self, body):
        new_body = Body([])
        _ = in_env(NEWBODY, new_body, lambda: self.mutate('stmts'))
        return new_body

    def t_Stmt(self, stmt):
        stmt = self.mutate()
        push_newbody(stmt)
        return stmt

    def Nop(self, s):
        # don't push
        return s

    def BlockMatch(self, bm):
        inVar = define_temp_var(self.mutate('expr'))
        add_extrinsic(Name, inVar, 'in')

        flatCases = []
        failProof = False
        for case in bm.cases:
            assert not failProof, "Fail-proof case isn't last?!"
            def go():
                f = flatten_pat(inVar, case.pat)
                body = vat.mutate(CompoundFlattener, case.result,'Body(LExpr)')
                return f, body

            testBody = Body([])
            failProof, body = in_env(NEWBODY, testBody, go)
            expandedCase = BlockCondCase(testBody, body)
            set_orig(expandedCase, case)
            flatCases.append(expandedCase)

        if not failProof:
            # could fall-through the last case, so add an "else" failure case
            matchFailure = Body([runtime_void_call('match_fail', [])])
            elseCase = BlockCondCase(Body([]), matchFailure)
            set_orig(elseCase, e)
            flatCases.append(elseCase)

        cond = BlockCond(flatCases)
        set_orig(cond, bm)
        push_newbody(cond)
        return cond

    def Match(self, e):
        inVar = define_temp_var(self.mutate('expr'))
        add_extrinsic(Name, inVar, 'in')

        outT = extrinsic(TypeOf, e)
        outInit = Undefined()
        add_extrinsic(TypeOf, outInit, outT)
        outVar = define_temp_var(outInit)
        add_extrinsic(Name, outVar, 'out')

        flatCases = []
        failProof = False
        for case in e.cases:
            assert not failProof, "Fail-proof case isn't last?!"
            testBody = Body([])
            failProof = in_env(NEWBODY, testBody, lambda:
                    flatten_pat(inVar, case.pat))

            resultBody = store_scope_result(outVar, lambda:
                    vat.mutate(CompoundFlattener, case.result, 'LExpr'))

            expandedCase = BlockCondCase(testBody, resultBody)
            set_orig(expandedCase, case)
            flatCases.append(expandedCase)

        if not failProof:
            # could fall-through the last case, so add an "else" failure case
            matchFailure = Body([runtime_void_call('match_fail', [])])
            elseCase = BlockCondCase(Body([]), matchFailure)
            set_orig(elseCase, e)
            flatCases.append(elseCase)

        cond = BlockCond(flatCases)
        set_orig(cond, e)
        push_newbody(cond)

        outBind = L.Bind(outVar)
        add_extrinsic(TypeOf, outBind, outT)
        return outBind

    def And(self, e):
        left = self.mutate('left')
        tmp = define_temp_var(left)
        thenBlock = store_scope_result(tmp, lambda: self.mutate('right'))
        bindTmp = L.Bind(tmp)
        add_extrinsic(TypeOf, bindTmp, TBool())
        then = CondCase(bindTmp, thenBlock)
        set_orig(then, e.right)
        cond = S.Cond([then])
        set_orig(cond, e)
        push_newbody(cond)

        output = L.Bind(tmp)
        add_extrinsic(TypeOf, output, TBool())
        return output

    def Or(self, e):
        left = self.mutate('left')
        tmp = define_temp_var(left)
        thenBlock = store_scope_result(tmp, lambda: self.mutate('right'))
        bindTmp = L.Bind(tmp)
        add_extrinsic(TypeOf, bindTmp, TBool())
        then = CondCase(builtin_call('not', [bindTmp]), thenBlock)
        set_orig(then, e.right)
        cond = S.Cond([then])
        set_orig(cond, e)
        push_newbody(cond)

        output = L.Bind(tmp)
        add_extrinsic(TypeOf, output, TBool())
        return output

    def Ternary(self, e):
        retType = extrinsic(TypeOf, e)
        undef = Undefined()
        add_extrinsic(TypeOf, undef, retType)
        result = define_temp_var(undef)
        test = self.mutate('test')
        trueBlock = store_scope_result(result, lambda: self.mutate('then'))
        falseBlock = store_scope_result(result, lambda: self.mutate('else_'))
        trueCase = CondCase(test, trueBlock)
        falseCase = CondCase(bind_true(), falseBlock)
        set_orig(trueCase, e.then)
        set_orig(falseCase, e.else_)
        cond = S.Cond([trueCase, falseCase])
        set_orig(cond, e)
        push_newbody(cond)
        output = L.Bind(result)
        add_extrinsic(TypeOf, output, retType)
        return output

def define_temp_var(init):
    t = extrinsic(TypeOf, init)
    var = Var()
    add_extrinsic(TypeOf, var, t)
    pat = PatVar(var)
    add_extrinsic(TypeOf, pat, t)
    push_newbody(S.Defn(pat, init))
    return var

def cast_to_ctor(inVar, ctor):
    inT = extrinsic(TypeOf, inVar)
    ctorT = TCtor(ctor, inT.appTypes)
    bind = L.Bind(inVar)
    add_extrinsic(TypeOf, bind, inT)

    var = Var()
    add_extrinsic(Name, var, extrinsic(Name, ctor).lower())
    add_extrinsic(TypeOf, var, ctorT)
    pat = PatVar(var)
    add_extrinsic(TypeOf, pat, ctorT)
    add_extrinsic(TypeCast, pat, (inT, ctorT))
    push_newbody(S.Defn(pat, bind))
    return var

def store_scope_result(var, func):
    body = Body([])
    result = in_env(NEWBODY, body, func)
    body.stmts.append(S.Assign(LhsVar(var), result))
    return body

def builtin_call(name, args):
    f = BUILTINS[name]
    ft = extrinsic(TypeOf, f)
    bind = L.Bind(f)
    add_extrinsic(TypeOf, bind, ft)
    call = L.Call(bind, args)
    add_extrinsic(TypeOf, call, ft.result.type)
    return call

def runtime_void_call(name, args):
    f = RUNTIME[name]
    b = L.Bind(f)
    add_extrinsic(TypeOf, b, extrinsic(TypeOf, f))
    return S.VoidStmt(VoidCall(b, args))

def bind_var(var):
    bind = L.Bind(var)
    add_extrinsic(TypeOf, bind, extrinsic(TypeOf, var))
    return bind

def bind_true():
    bind = L.Bind(BUILTINS['True'])
    add_extrinsic(TypeOf, bind, TBool())
    return bind

# PATTERN MATCHING

def flatten_pat(inVar, origPat):
    m = match(origPat)
    if m('PatVar(var)'):
        push_newbody(S.Defn(origPat, bind_var(inVar)))
        return True
    elif m('PatWild()'):
        return True
    elif m('PatCtor(ctor, args)'):

        # XXX maybe codegen
        if Nullable.isMaybe(m.ctor):
            return flatten_pat_maybe(inVar, origPat, m.args)

        failProof = True
        if has_extrinsic(CtorIndex, m.ctor):
            failProof = False

            inVar = cast_to_ctor(inVar, m.ctor)

            # check ix, fall-through if failed
            readIx = AttrIx(bind_var(inVar))
            add_extrinsic(TypeOf, readIx, TInt())
            index = L.Lit(IntLit(extrinsic(CtorIndex, m.ctor)))
            add_extrinsic(TypeOf, index, TInt())
            ixTest = builtin_call('!=', [readIx, index])
            ixCheck = NextCase(ixTest)
            set_orig(ixCheck, origPat)
            push_newbody(ixCheck)

        for field, argPat in ezip(m.ctor.fields, m.args):

            # dumb special case shortcut
            # should really write this inside-out or by-need to avoid
            # capturing values I don't need
            if matches(argPat, 'PatWild()'):
                continue

            # read attr from input object
            argT = extrinsic(TypeOf, argPat)
            fieldValue = L.Attr(bind_var(inVar), field)
            add_extrinsic(TypeOf, fieldValue, argT)
            fieldVar = define_temp_var(fieldValue)
            add_extrinsic(Name, fieldVar, extrinsic(Name, field))
            # match against its value recursively
            if not flatten_pat(fieldVar, argPat):
                failProof = False
        return failProof

    elif m('PatTuple(pats)'):
        # extract tuple values with tmp defn
        defnVars = []
        defnPats = []
        subPats = m.pats
        for i, subPat in enumerate(subPats):
            t = extrinsic(TypeOf, subPat)

            m = match(subPat)
            if m('PatWild()'):
                # once again, dumb hacky shortcut
                defnVars.append(None)
                m.ret(PatWild())
            else:
                v = Var()
                add_extrinsic(Name, v, 'tup%d' % (i,))
                add_extrinsic(TypeOf, v, t)
                defnVars.append(v)
                m.ret(PatVar(v))
            dPat = m.result()
            add_extrinsic(TypeOf, dPat, t)
            defnPats.append(dPat)
        defnTuple = PatTuple(defnPats)
        add_extrinsic(TypeOf, defnTuple, extrinsic(TypeOf, origPat))
        push_newbody(S.Defn(defnTuple, bind_var(inVar)))

        # now recurse with these bindings
        failProof = True
        for defnVar, subPat in ezip(defnVars, subPats):
            if defnVar is not None:
                if not flatten_pat(defnVar, subPat):
                    failProof = False
        return failProof

    elif m('PatInt(val)'):
        # check ix, fall-through if failed
        readInt = bind_var(inVar)
        lit = L.Lit(IntLit(m.val))
        add_extrinsic(TypeOf, lit, TInt())
        intTest = builtin_call('!=', [readInt, lit])
        intCheck = NextCase(intTest)
        set_orig(intCheck, origPat)
        push_newbody(intCheck)
        return False
    else:
        assert False, "Can't handle pattern %s yet" % (origPat,)

def flatten_pat_maybe(inVar, origPat, args):
    maybeT = extrinsic(TypeOf, inVar)
    readPtr = bind_var(inVar)
    nullPtr = NullPtr()
    add_extrinsic(TypeOf, nullPtr, maybeT)

    if len(args) == 1:
        subPat = args[0]
        nullCheck = builtin_call('==', [readPtr, nullPtr])
        failCheck = NextCase(nullCheck)
        set_orig(failCheck, origPat)
        push_newbody(failCheck)

        if not matches(subPat, 'PatWild()'): # bah hack
            t = extrinsic(TypeOf, subPat)
            castBind = bind_var(inVar)
            update_extrinsic(TypeOf, castBind, t)
            add_extrinsic(TypeCast, castBind, (maybeT, t))
            castedVar = define_temp_var(castBind)
            add_extrinsic(Name, castedVar, 'just')
            flatten_pat(castedVar, subPat)
    else:
        assert len(args) == 0
        nullCheck = builtin_call('!=', [readPtr, nullPtr])
        failCheck = NextCase(nullCheck)
        set_orig(failCheck, origPat)
        push_newbody(failCheck)

    return False

def flatten_unit(unit):
    vat.mutate(CompoundFlattener, unit, t_DT(ExpandedUnit))
    return build_control_flow(unit)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
