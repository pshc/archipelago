from base import *
from atom import *
from quilt import *
import runtime
import vat

CFGFuncState = DT('CFGFuncState',
        ('pendingExits', {int: ['*Block']}),
        ('gcVars', ['*Var']),
        ('pastBlocks', [Block]))

CFGFUNC = new_env('CFGFUNC', CFGFuncState)

CFGScopeState = DT('CFGScopeState',
        ('block', 'Maybe(Block)'),
        ('level', int),
        ('livenessByLevel', {int: ['*Var']}),
        ('prevScope', 'Maybe(*CFGScopeState)'))

CFG = new_env('CFG', CFGScopeState)

LoopInfo = DT('LoopInfo', ('level', int), ('entryBlock', '*Block'))

LOOP = new_env('LOOP', LoopInfo)

NextCaseInfo = DT('NextCaseInfo', ('failProof', bool),
                                  ('exitLevel', int),
                                  ('nextBlock', 'Maybe(*Block)'))

NEXTCASE = new_env('NEXTCASE', NextCaseInfo)

NEWFUNCS = new_env('NEWFUNCS', [BlockFunc])

def empty_block(label, index):
    label = '%s.%d' % (label, index)
    return Block(label, [], [], TermJump(Nothing()), [])

def start_new_block(label, index):
    "Closes up the current block if any, then returns a fresh one."
    new = empty_block(label, index)
    cfg = env(CFG)
    m = match(cfg.block)
    if m('Just(block)'):
        old = m.block
        jumps(old, new)
        env(CFGFUNC).pastBlocks.append(old)
    cfg.block = Just(new)
    resolve_pending_exits(new)
    return new

def block_push(stmt):
    m = match(env(CFG).block)
    if m('Just(block)'):
        m.block.stmts.append(stmt)

def jumps(src, dest):
    assert matches(src.terminator, 'TermJump(Nothing())'), \
            "Block %s's terminator already resolved?!" % (src,)
    src.terminator = TermJump(Just(dest))
    dest.entryBlocks.append(src)

def flip_jump(test, true, false, converse):
    if converse:
        return TermJumpCond(test, false, true)
    else:
        return TermJumpCond(test, true, false)

def resolve_pending_exits(destBlock):
    level = env(CFG).level
    pendingExits = env(CFGFUNC).pendingExits
    if level not in pendingExits:
        return
    pending = pendingExits[level]
    del pendingExits[level]
    for block in pending:
        m = match(block.terminator)
        if m('TermJumpCond(_, Nothing(), Just(_))'):
            block.terminator.trueDest = Just(destBlock)
            destBlock.entryBlocks.append(block)
        elif m('TermJumpCond(_, Just(_), Nothing())'):
            block.terminator.falseDest = Just(destBlock)
            destBlock.entryBlocks.append(block)
        elif m('TermJump(Nothing())'):
            jumps(block, destBlock)
        else:
            assert False, "Can't resolve %s" % (block.terminator,)

def is_gc_var(var):
    t = extrinsic(TypeOf, var)
    if not is_strong_type(t):
        return False
    m = match(t)
    if m('TArray(_, kind)'):
        return matches(m.kind, 'AGC()')
    elif m('TFunc(_, _, _)'):
        return False
    else:
        return True

def live_vars_exist_since_level(notIncludedLevel):
    cfg = env(CFG)
    if isNothing(cfg.block):
        return False

    nullOuts = fromJust(cfg.block).nullOuts
    level = cfg.level
    liveness = cfg.livenessByLevel
    while level > notIncludedLevel:
        if level in liveness:
            assert len(liveness[level]) > 0
            return True
        level -= 1
    return False

def destroy_vars_until_level(exitLevel):
    cfg = env(CFG)
    if isNothing(cfg.block):
        return

    nullOuts = fromJust(cfg.block).nullOuts
    level = cfg.level
    liveness = cfg.livenessByLevel
    while level > exitLevel:
        if level in liveness:
            for var in liveness[level]:
                if is_gc_var(var):
                    nullOuts.append(var)
            del liveness[level]
        level -= 1

def finish_block(term):
    "Closes up the current block with a terminator."
    cfg = env(CFG)
    if isNothing(cfg.block):
        return
    finished = fromJust(cfg.block)
    assert matches(finished.terminator, 'TermJump(Nothing())')
    finished.terminator = term
    env(CFGFUNC).pastBlocks.append(finished)
    cfg.block = Nothing()

def finish_jump(block):
    "Finishes with TermJump and also updates entryBlock on the dest block."
    cfg = env(CFG)
    if isNothing(cfg.block):
        return
    block.entryBlocks.append(fromJust(cfg.block))
    finish_block(TermJump(Just(block)))

def pend_exit(block, level):
    env(CFGFUNC).pendingExits.setdefault(level, []).append(block)

def exit_to_level(level):
    "Terminates current block, later resolving to the next block at level."
    cfg = env(CFG)
    if isNothing(cfg.block):
        return
    block = fromJust(cfg.block)
    assert level <= cfg.level, "Bad exit to inner level"
    pend_exit(block, level)
    env(CFGFUNC).pastBlocks.append(block)
    cfg.block = Nothing()

def build_body(body, callInside):
    def go():
        for stmt in body.stmts:
            vat.visit(ControlFlowBuilder, stmt, 'Stmt(LExpr)')
        callInside()
        assert isNothing(env(CFG).block), "Block still active after scope end"
    inside_cfg_scope(go)
    env(CFG).block = Nothing()

def inside_cfg_scope(callInside):
    outer = env(CFG)
    liveness = outer.livenessByLevel.copy()
    # allow cur block to bleed into inner scope
    inner = CFGScopeState(outer.block, outer.level+1, liveness, outer)
    in_env(CFG, inner, callInside)
    assert inner.level not in env(CFGFUNC).pendingExits, "Dangling exit?"

def build_body_and_exit_to_level(body, exitLevel):
    def leave():
        destroy_vars_until_level(exitLevel)
        exit_to_level(exitLevel)
    build_body(body, leave)

def orig_index(stmt):
    return vat.orig_loc(stmt).index

class ControlFlowBuilder(vat.Visitor):
    def TopFunc(self, top):
        # params are considered alive during the entire function for now
        # so don't bother tracking their liveness
        lives = {}

        topScope = CFGScopeState(Just(empty_block('', 0)), 0, lives, Nothing())
        funcInfo = CFGFuncState({}, [], [])

        def finish_func():
            finish_block(TermReturnNothing())
            assert not funcInfo.pendingExits, "CFG dangling exits: %s" % (
                    funcInfo.pendingExits,)

        in_env(CFGFUNC, funcInfo, lambda: in_env(CFG, topScope,
                lambda: build_body(top.func.body, finish_func)))

        blocks = funcInfo.pastBlocks
        if len(blocks) == 0:
            b = empty_block('', 0)
            b.terminator = TermReturnNothing()
            blocks.append(b)

        params = map(LVar, top.func.params)
        # params might need to also be in gcVars?
        bf = BlockFunc(top.var, funcInfo.gcVars, params, blocks)
        env(NEWFUNCS).append(bf)

    def FuncExpr(self, fe):
        assert False, "FuncExprs ought to be gone"

    def Body(self, body):
        assert False, "Use custom body handlers"

    def Break(self, stmt):
        level = env(LOOP).level
        destroy_vars_until_level(level)
        exit_to_level(level)

    def BreakUnless(self, stmt):
        cfg = env(CFG)
        curBlock = fromJust(cfg.block)

        keepGoingBlock = empty_block('whilebody', orig_index(stmt))
        keepGoingBlock.entryBlocks.append(curBlock)
        keepGoing = Just(keepGoingBlock)

        exitLevel = env(LOOP).level
        needDestruction = live_vars_exist_since_level(exitLevel)
        if needDestruction:
            # (gc'd object obtained in while's test expr needs destruction)
            destructBlock = empty_block('breakcleanup', orig_index(stmt))
            destructBlock.entryBlocks.append(curBlock)
            destruct = Just(destructBlock)
            finish_block(TermJumpCond(stmt.test, keepGoing, destruct))
            cfg.block = destruct
            # need to emulate a scope here since BreakUnless is Body-less
            inside_cfg_scope(lambda: destroy_vars_until_level(exitLevel))
            exit_to_level(exitLevel)
        else:
            finish_block(TermJumpCond(stmt.test, keepGoing, Nothing()))
            pend_exit(curBlock, exitLevel)

        cfg.block = keepGoing

    def NextCase(self, stmt):
        cfg = env(CFG)
        curBlock = fromJust(cfg.block)
        test, converse = elide_NOTs(stmt.test)
        nc = env(NEXTCASE)

        # yep, backwards
        cannotGotoNextCase = matches(test, 'Bind(key("True"))') if converse \
                else matches(test, 'Bind(key("False"))')
        if cannotGotoNextCase:
            return # although an upcoming NextCase stmt *could*

        successBlock = empty_block('notok' if converse else 'ok',
                orig_index(stmt))
        successBlock.entryBlocks.append(curBlock)
        success = Just(successBlock)
        nc.failProof = False

        needDestruction = live_vars_exist_since_level(nc.exitLevel)
        failBlock = Just(empty_block('casecleanup', orig_index(stmt))) \
                if needDestruction else Nothing()

        haveNextBlock = isJust(nc.nextBlock)
        if haveNextBlock and not needDestruction:
            failBlock = nc.nextBlock

        finish_block(flip_jump(test, failBlock, success, converse))
        if isJust(failBlock):
            fromJust(failBlock).entryBlocks.append(curBlock)

        if needDestruction:
            cfg.block = failBlock
            # need to emulate a scope here since NextCase is Body-less
            inside_cfg_scope(lambda: destroy_vars_until_level(nc.exitLevel))

            if haveNextBlock:
                finish_jump(fromJust(nc.nextBlock))
            else:
                exit_to_level(nc.exitLevel)
        elif not haveNextBlock:
            pend_exit(curBlock, nc.exitLevel)

        cfg.block = success

    def BlockCond(self, cond):
        cfg = env(CFG)
        exitLevel = cfg.level
        n = len(cond.cases)

        for i, case in enumerate(cond.cases):
            assert isJust(cfg.block), "Unreachable case %s?" % (case,)

            isLast = (i == n-1)
            if not isLast:
                nextTest = empty_block('elif', orig_index(cond.cases[i+1]))
                info = NextCaseInfo(True, exitLevel, Just(nextTest))
            else:
                block = fromJust(cfg.block)
                if block.label[:4] == 'elif':
                    block.label = 'else' + block.label[4:]
                info = NextCaseInfo(True, exitLevel, Nothing())

            def after_tests():
                assert not info.failProof or isLast
                build_body_and_exit_to_level(case.body, exitLevel)
            in_env(NEXTCASE, info, lambda: build_body(case.test, after_tests))
            cfg.block = info.nextBlock

        if exitLevel in env(CFGFUNC).pendingExits:
            _ = start_new_block('endif', orig_index(cond))

    def Cond(self, cond):
        cfg = env(CFG)
        pendingExits = env(CFGFUNC).pendingExits
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
            test, converse = elide_NOTs(case.test)
            true = empty_block('notthen' if converse else 'then',
                    orig_index(case))

            nextTest = Nothing() if isLast else \
                    Just(empty_block('elif', orig_index(cond.cases[i+1])))

            jump = flip_jump(test, Just(true), nextTest, converse)
            curBlock = fromJust(cfg.block)
            true.entryBlocks.append(curBlock)
            if isLast:
                # resolve the conditional fall-through later
                pends = pendingExits.setdefault(exitLevel, [])
                pends.append(curBlock)
            else:
                fromJust(nextTest).entryBlocks.append(curBlock)
            finish_block(jump)
            cfg.block = Just(true)
            build_body_and_exit_to_level(case.body, exitLevel)
            cfg.block = nextTest

        if exitLevel in pendingExits:
            _ = start_new_block('endif', orig_index(cond))

    def Continue(self, stmt):
        loop = env(LOOP)
        destroy_vars_until_level(loop.level)
        finish_jump(loop.entryBlock)

    def Return(self, stmt):
        env(CFG).livenessByLevel = {}
        finish_block(TermReturn(stmt.expr))

    def ReturnNothing(self, stmt):
        env(CFG).livenessByLevel = {}
        finish_block(TermReturnNothing())

    def While(self, stmt):
        cfg = env(CFG)
        exitLevel = cfg.level
        start = start_new_block('while', orig_index(stmt))
        in_env(LOOP, LoopInfo(exitLevel, start),
                lambda: build_body(stmt.body, lambda: finish_jump(start)))

        assert matches(stmt.test, 'Undefined()')
        if exitLevel in env(CFGFUNC).pendingExits:
            # there was a break somewhere, so resolve it to here
            _ = start_new_block('endwhile', orig_index(stmt))

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
        if matches(extrinsic(ResultOf, stmt), "Bottom()"):
            # this is dumb...
            # we can't clobber vars since they might be call args.
            # ideally this would be some kind of tail call that overwrites
            # this stack frame.
            # anyway, currently Bottom calls are only for failed asserts,
            # so whatever.
            #destroy_vars_until_level(0)
            finish_block(TermUnreachable())

    # ugh what is this doing here
    def PushEnv(self, stmt):
        block_push(stmt)
    def PopEnv(self, stmt):
        block_push(stmt)
    def WriteExtrinsic(self, stmt):
        block_push(stmt)

    def t_Stmt(self, stmt):
        assert False, "Can't deal with %s" % stmt

    def Var(self, var):
        if not is_gc_var(var):
            return
        cfg = env(CFG)
        cfg.livenessByLevel.setdefault(cfg.level, []).append(var)

        env(CFGFUNC).gcVars.append(var)

def negate(expr):
    m = match(expr)
    if m('Call(Bind(key("not")), [e])'):
        return m.e
    else:
        return builtin_call('not', [expr])

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
        if m('TermJump(Just(dest))'):
            assert src in m.dest.entryBlocks
            entryCounts[m.dest] = entryCounts.get(m.dest, 0) + 1
        elif m('TermJumpCond(_, Just(d1), Just(d2))'):
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
                    ('TermJump(Just(d))', lambda d: 'j %s' % (d.label,)),
                    ('TermJumpCond(c, Just(t), Just(f))', lambda c, t, f:
                        'j %r, %s, %s' % (c, t.label, f.label)),
                    ('TermReturnNothing()', lambda: 'ret void'),
                    ('TermReturn(e)', lambda e: 'ret %r' % (e,)),
                    ('TermUnreachable()', lambda: 'unreachable'))
            print

    map_(check_cfg_func, funcs)
    return BlockUnit(funcs)

NEWBODY = new_env('NEWBODY', Body)

ExprPurity, PureExpr, ImpureExpr, UniqueVar, ThanksForTheVar = \
    ADT('ExprPurity',
        'PureExpr', ('expr', LExpr),
        'ImpureExpr', ('expr', LExpr),
        'UniqueVar', ('var', Var),
        'ThanksForTheVar')

def push_newbody(s):
    env(NEWBODY).stmts.append(s)

# way too many of these helpers!

def spill_to_pure(expr):
    m = match(expr)
    if m('PureExpr(_) or UniqueVar(_)'):
        return expr
    elif m('ImpureExpr(expr)'):
        return UniqueVar(define_temp_var(m.expr))
    else:
        assert False

def spill_lower(expr):
    m = match(flatten_expr(expr, Nothing()))
    if m('PureExpr(expr)'):
        return m.expr
    elif m('ImpureExpr(expr)'):
        return bind_var(define_temp_var(m.expr))
    elif m('UniqueVar(var)'):
        return bind_var(m.var)
    else:
        assert False

def store_scope_result(destVar, expr):
    body = Body([])
    in_env(NEWBODY, body, lambda: store_result(destVar, expr))
    return body

def store_result(destVar, expr):
    m = match(flatten_expr(expr, Just(destVar)))
    if m('PureExpr(expr) or ImpureExpr(expr)'):
        push_newbody(S.Assign(LhsVar(destVar), m.expr))
    elif m('ThanksForTheVar()'):
        pass # already taken care of!
    elif m('UniqueVar(var)'):
        # result showed up in a different var for some reason?
        assert destVar is not m.var
        push_newbody(S.Assign(LhsVar(destVar), m.var))

def flatten_expr_to_var(expr, optVar):
    m = match(flatten_expr(expr, optVar))
    if m('ThanksForTheVar()'):
        return fromJust(optVar)
    elif m('UniqueVar(var)'):
        return m.var
    elif m('PureExpr(e) or ImpureExpr(e)'):
        return define_temp_var(m.e)

@annot('(LExpr, Maybe(Var)) -> ExprPurity')
def flatten_expr(expr, optVar):
    haveOutVar = isJust(optVar)
    m = match(expr)
    if m('And(left, right)'):
        tmp = flatten_expr_to_var(m.left, optVar)
        thenBlock = store_scope_result(tmp, m.right)
        then = CondCase(bind_var_typed(tmp, TBool()), thenBlock)
        set_orig(then, m.right)
        cond = S.Cond([then])
        set_orig(cond, expr)
        push_newbody(cond)
        return UniqueVar(tmp)

    elif m('Or(left, right)'):
        tmp = flatten_expr_to_var(m.left, optVar)
        thenBlock = store_scope_result(tmp, m.right)
        then = CondCase(negate(bind_var_typed(tmp, TBool())), thenBlock)
        set_orig(then, m.right)
        cond = S.Cond([then])
        set_orig(cond, expr)
        push_newbody(cond)
        return UniqueVar(tmp)

    elif m('Ternary(test, then, else_)'):
        if haveOutVar:
            result = fromJust(optVar)
            retVal = ThanksForTheVar()
        else:
            undef = Undefined()
            add_extrinsic(TypeOf, undef, extrinsic(TypeOf, expr))
            result = define_temp_var(undef)
            retVal = UniqueVar(result)
        test = spill_lower(m.test)
        trueBlock = store_scope_result(result, m.then)
        falseBlock = store_scope_result(result, m.else_)
        trueCase = CondCase(test, trueBlock)
        falseCase = CondCase(bind_true(), falseBlock)
        set_orig(trueCase, m.then)
        set_orig(falseCase, m.else_)
        cond = S.Cond([trueCase, falseCase])
        set_orig(cond, expr)
        push_newbody(cond)
        return retVal

    elif m('Match(expr, cases)'):
        inVar = flatten_expr_to_var(m.expr, optVar)
        add_extrinsic(Name, inVar, 'in')

        if haveOutVar:
            outVar = fromJust(optVar)
            retVal = ThanksForTheVar()
        else:
            outInit = Undefined()
            add_extrinsic(TypeOf, outInit, extrinsic(TypeOf, expr))
            outVar = define_temp_var(outInit)
            add_extrinsic(Name, outVar, 'out')
            retVal = UniqueVar(outVar)

        flatCases = []
        failProof = False
        for case in m.cases:
            assert not failProof, "Fail-proof case isn't last?!"
            testBody = Body([])
            failProof = in_env(NEWBODY, testBody, lambda:
                    flatten_pat(inVar, case.pat))

            resultBody = store_scope_result(outVar, case.result)

            expandedCase = BlockCondCase(testBody, resultBody)
            set_orig(expandedCase, case)
            flatCases.append(expandedCase)

        if not failProof:
            # could fall-through the last case, so add an "else" failure case
            matchFail = runtime_void_call('fail_with_code',
                    [int_lit(runtime.FAIL_BAD_MATCH)])
            elseCase = BlockCondCase(Body([]), Body([matchFail]))
            set_orig(elseCase, expr)
            flatCases.append(elseCase)

        cond = BlockCond(flatCases)
        set_orig(cond, expr)
        push_newbody(cond)

        return retVal

    elif m('Call(func, args)'):
        target = match(expr.func, "Bind(target)")
        expr.args = map(spill_lower, m.args)
        # type hack
        if matches(target, "Builtin()"):
            return PureExpr(expr)
        # XXX maybe codegen
        if Nullable.isMaybe(target):
            return PureExpr(expr)
        return ImpureExpr(expr)
    elif m('CallIndirect(func, args, _)'):
        # only thing to worry about for expr.func
        # is reassignable function pointers
        assert matches(expr.func, "Bind(_)")
        expr.args = map(spill_lower, m.args)
        return ImpureExpr(expr)

    elif m('Bind(_)'):
        # if closures are allowed to reassign vars, this will have to spill
        return PureExpr(expr)
    elif m('Lit(_)'):
        return PureExpr(expr)
    elif m('FuncVal(_, _)'):
        # todo: ctx capture semantics (would need to be impure if captured)
        return PureExpr(expr)

    # though trivial, these need to guarantee order relative to siblings
    elif m('Attr(expr, _)'):
        expr.expr = spill_lower(m.expr)
        return ImpureExpr(expr)
    elif m('TupleLit(vals)'):
        expr.vals = map(spill_lower, m.vals)
        return ImpureExpr(expr)
    elif m('ListLit(vals)'):
        expr.vals = map(spill_lower, m.vals)
        return ImpureExpr(expr)

    elif m('GetEnv(_) or HaveEnv(_)'):
        return ImpureExpr(expr)
    elif m('InEnv(env, init, expr)'):
        push = PushEnv(m.env, spill_lower(m.init))
        set_orig(push, expr)
        push_newbody(push)

        ret = spill_to_pure(flatten_expr(m.expr, Nothing()))

        pop = PopEnv(m.env)
        set_orig(pop, expr)
        push_newbody(pop)
        return ret
    elif m('CreateCtx(_, init)'): # TEMP
        expr.init = spill_lower(m.init)
        return ImpureExpr(expr)
    elif m('DestroyCtx(_, ctx)'):
        expr.ctx = spill_lower(m.ctx)
        return ImpureExpr(expr)

    elif m('GetExtrinsic(_, e) or HasExtrinsic(_, e)'):
        expr.node = spill_lower(m.e)
        return ImpureExpr(expr)
    elif m('ScopeExtrinsic(_, e)'):
        expr.expr = spill_lower(m.e)
        return ImpureExpr(expr)

    else:
        assert False, "Can't deal with %s" % (expr)

def flatten_void_expr(ve, result):
    m = match(ve)
    if m('VoidCall(Bind(_), args)'):
        ve.args = map(spill_lower, m.args)
        stmt = S.VoidStmt(ve)
        add_extrinsic(ResultOf, stmt, result)
        push_newbody(stmt)
    elif m('VoidInEnv(env, init, expr)'):
        push = PushEnv(m.env, spill_lower(m.init))
        set_orig(push, ve)
        push_newbody(push)
        flatten_void_expr(m.expr, result)
        # NOTE: if result is Bottom, we'll never get here
        pop = PopEnv(m.env)
        set_orig(pop, ve)
        push_newbody(pop)
    else:
        assert False

def flatten_stmt(stmt):
    m = match(stmt)
    if m('Assign(_, e) or AugAssign(_, _, e)'):
        stmt.expr = spill_lower(m.e)
        push_newbody(stmt)
    elif m('Break() or Continue()'):
        push_newbody(stmt)
    elif m('Cond(cases)'):
        # Turn this into a BlockCond
        newCases = []
        for case in m.cases:
            def go_test():
                test, converse = elide_NOTs(case.test)
                notTest = spill_lower(test if converse else negate(test))
                testStmt = NextCase(notTest)
                set_orig(testStmt, case)
                push_newbody(testStmt)

            testBody = Body([])
            in_env(NEWBODY, testBody, go_test)
            resultBody = flatten_body(case.body)
            newCase = BlockCondCase(testBody, resultBody)
            set_orig(newCase, case)
            newCases.append(newCase)
        blockCond = BlockCond(newCases)
        set_orig(blockCond, stmt)
        push_newbody(blockCond)

    elif m('Defn(PatWild(), e)'):
        # silly special case
        m = match(flatten_expr(m.e, Nothing()))
        if m('ImpureExpr(expr)'):
            stmt.expr = m.expr
            push_newbody(stmt)
        elif not m('PureExpr(_) or UniqueVar(_)'):
            assert False, "need to spill impurities"
    elif m('Defn(pat, e)'):
        stmt.expr = spill_lower(m.e)
        push_newbody(stmt)
    elif m('Return(e)'):
        stmt.expr = spill_lower(m.e)
        push_newbody(stmt)
    elif m('ReturnNothing()'):
        push_newbody(stmt)

    elif m('While(test, body)'):
        def go():
            assert not matches(m.test, 'Bind(key("False"))'), 'while False?'
            if not matches(m.test, 'Bind(key("True"))'):
                breaker = BreakUnless(spill_lower(m.test))
                set_orig(breaker, m.test)
                push_newbody(breaker)

            map_(flatten_stmt, m.body.stmts)

        whileBody = Body([])
        in_env(NEWBODY, whileBody, go)
        stmt.test = Undefined() # irrelevant due to flattening above
        stmt.body = whileBody
        push_newbody(stmt)

    elif m('BlockMatch(expr, cases)'):
        inVar = flatten_expr_to_var(m.expr, Nothing())
        add_extrinsic(Name, inVar, 'in')

        flatCases = []
        failProof = False
        for case in m.cases:
            assert not failProof, "Fail-proof case isn't last?!"
            def go():
                f = flatten_pat(inVar, case.pat)
                body = flatten_body(case.result)
                return f, body

            testBody = Body([])
            failProof, body = in_env(NEWBODY, testBody, go)
            expandedCase = BlockCondCase(testBody, body)
            set_orig(expandedCase, case)
            flatCases.append(expandedCase)

        if not failProof:
            # could fall-through the last case, so add an "else" failure case
            matchFail = runtime_void_call('fail_with_code',
                    [int_lit(runtime.FAIL_BAD_MATCH)])
            elseCase = BlockCondCase(Body([]), Body([matchFail]))
            set_orig(elseCase, stmt)
            flatCases.append(elseCase)

        cond = BlockCond(flatCases)
        set_orig(cond, stmt)
        push_newbody(cond)

    elif m('VoidStmt(voidExpr)'):
        flatten_void_expr(m.voidExpr, extrinsic(ResultOf, stmt))

    elif m('WriteExtrinsic(_, node, val, _)'):
        stmt.node = spill_lower(m.node)
        stmt.val = spill_lower(m.val)
        push_newbody(stmt)

    elif m('Nop()'):
        pass
    else:
        assert False, "Can't deal with %s" % (stmt,)

def flatten_body(body):
    new_body = Body([])
    in_env(NEWBODY, new_body, lambda: map_(flatten_stmt, body.stmts))
    return new_body

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
    bind = bind_var_typed(inVar, inT)

    var = Var()
    add_extrinsic(Name, var, extrinsic(Name, ctor).lower())
    add_extrinsic(TypeOf, var, ctorT)
    pat = PatVar(var)
    add_extrinsic(TypeOf, pat, ctorT)
    add_extrinsic(TypeCast, pat, (inT, ctorT))
    push_newbody(S.Defn(pat, bind))
    return var

def builtin_call(name, args):
    f = BUILTINS[name]
    ft = extrinsic(TypeOf, f)
    call = L.Call(bind_var_typed(f, ft), args)
    add_extrinsic(TypeOf, call, ft.result.type)
    return call

def runtime_void_call(name, args):
    f = RUNTIME[name]
    stmt = S.VoidStmt(VoidCall(bind_var(f), args))
    add_extrinsic(ResultOf, stmt, extrinsic(TypeOf, f).result)
    return stmt

def bind_var(var):
    bind = L.Bind(var)
    add_extrinsic(TypeOf, bind, extrinsic(TypeOf, var))
    return bind

def bind_var_typed(var, t):
    bind = L.Bind(var)
    add_extrinsic(TypeOf, bind, t)
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
            index = int_lit(extrinsic(CtorIndex, m.ctor))
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

            # if there's a cast, it'll be done later by LLVMPatCast handling
            # we just need to make sure the input type is correct here
            if has_extrinsic(TypeCast, argPat):
                src, dest = extrinsic(TypeCast, argPat)
                argT = src
            else:
                argT = extrinsic(TypeOf, argPat)

            # read attr from input object
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
        lit = int_lit(m.val)
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

def int_lit(n):
    lit = L.Lit(IntLit(n))
    add_extrinsic(TypeOf, lit, TInt())
    return lit

def flatten_unit(unit):
    for topFunc in unit.funcs:
        topFunc.func.body = flatten_body(topFunc.func.body)
    return build_control_flow(unit)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
