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

# really should be an ADT (either nextBlock or exitLevel)
NextCaseInfo = DT('NextCaseInfo', ('failProof', bool),
                                  ('exitLevel', int),
                                  ('nextBlock', 'Maybe(*Block)'))

NEXTCASE = new_env('NEXTCASE', NextCaseInfo)

NEWFUNCS = new_env('NEWFUNCS', [BlockFunc])

def initial_cfg_state():
    return ControlFlowState(Just(empty_block('', 0)), 0, {}, [], [], [])

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
        cfg.pastBlocks.append(old)
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

def resolve_pending_exits(destBlock):
    cfg = env(CFG)
    level = cfg.level
    if level not in cfg.pendingExits:
        return
    pending = cfg.pendingExits[level]
    del cfg.pendingExits[level]
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
    assert matches(finished.terminator, 'TermJump(Nothing())')
    finished.terminator = term
    cfg.pastBlocks.append(finished)
    cfg.block = Nothing()

def finish_jump(block):
    "Finishes with TermJump and also updates entryBlock on the dest block."
    cfg = env(CFG)
    if isNothing(cfg.block):
        return
    block.entryBlocks.append(fromJust(cfg.block))
    finish_block(TermJump(Just(block)))

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
        assert not state.pendingExits, "CFG dangling exits: %s" % (
                state.pendingExits,)
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

    def BreakUnless(self, stmt):
        cfg = env(CFG)
        curBlock = fromJust(cfg.block)

        keepGoingBlock = empty_block('whilebody', orig_index(stmt))
        keepGoingBlock.entryBlocks.append(curBlock)
        keepGoing = Just(keepGoingBlock)

        #null_out_scope_vars()
        finish_block(TermJumpCond(stmt.test, keepGoing, Nothing()))
        pends = cfg.pendingExits.setdefault(env(LOOP).level, [])
        pends.append(curBlock)
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

        successBlock = empty_block('ok', orig_index(stmt))
        successBlock.entryBlocks.append(curBlock)
        success = Just(successBlock)
        nc.failProof = False

        m = match(nc.nextBlock)
        if m('Just(block)'):
            m.block.entryBlocks.append(curBlock)
            #null_out_scope_vars()
            finish_block(TermJumpCond(test, success, nc.nextBlock) \
                    if converse else TermJumpCond(test, nc.nextBlock, success))
        else: # dumb hack again!
            assert nc.exitLevel != 0
            #null_out_scope_vars()
            finish_block(TermJumpCond(test, success, Nothing()) \
                    if converse else TermJumpCond(test, Nothing(), success))
            pends = cfg.pendingExits.setdefault(nc.exitLevel, [])
            pends.append(curBlock)

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
                info = NextCaseInfo(True, 0, Just(nextTest))
            else:
                block = fromJust(cfg.block)
                if block.label[:4] == 'elif':
                    block.label = 'else' + block.label[4:]
                info = NextCaseInfo(True, exitLevel, Nothing())

            in_env(NEXTCASE, info, lambda:
                    vat.visit(ControlFlowBuilder, case.test, 'Body(LExpr)'))
            assert not info.failProof or isLast
            build_body_and_exit_to_level(case.body, exitLevel)
            cfg.block = info.nextBlock

        if exitLevel in cfg.pendingExits:
            _ = start_new_block('endif', orig_index(cond))

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

            nextTest = Nothing() if isLast else \
                    Just(empty_block('elif', orig_index(cond.cases[i+1])))

            test, converse = elide_NOTs(case.test)
            jump = TermJumpCond(test, nextTest, Just(true)) if converse \
                    else TermJumpCond(test, Just(true), nextTest)
            curBlock = fromJust(cfg.block)
            true.entryBlocks.append(curBlock)
            if isLast:
                # resolve the conditional fall-through later
                pends = cfg.pendingExits.setdefault(exitLevel, [])
                pends.append(curBlock)
            else:
                fromJust(nextTest).entryBlocks.append(curBlock)
            finish_block(jump)
            cfg.block = Just(true)
            build_body_and_exit_to_level(case.body, exitLevel)
            cfg.block = nextTest

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
        def go():
            self.visit('body')
            finish_jump(start)
        in_env(LOOP, LoopInfo(exitLevel, start), go)

        assert matches(stmt.test, 'Undefined()')
        if exitLevel in cfg.pendingExits:
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
        if m('VoidCall(Bind(f), _)'):
            if matches(extrinsic(TypeOf, m.f), 'TFunc(_, Bottom(), _)'):
                null_out_scope_vars()
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
        cfg = env(CFG)
        cfg.scopeVars.append(var)
        if is_gc_var(var):
            cfg.gcVars.append(var)

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

ExprPurity, PureExpr, ImpureExpr, UniqueVar = \
    ADT('ExprPurity',
        'PureExpr', ('expr', LExpr),
        'ImpureExpr', ('expr', LExpr),
        'UniqueVar', ('var', Var))

def push_newbody(s):
    env(NEWBODY).stmts.append(s)

def spill(expr):
    m = match(expr)
    if m('PureExpr(_) or UniqueVar(_)'):
        return expr
    elif m('ImpureExpr(expr)'):
        return UniqueVar(define_temp_var(m.expr))

def gather_expr(expr):
    m = match(flatten_expr(expr, Nothing()))
    if m('PureExpr(expr)'):
        return m.expr
    elif m('ImpureExpr(expr)'):
        return bind_var(define_temp_var(m.expr))
    elif m('UniqueVar(var)'):
        return bind_var(m.var)

def store_scope_result(destVar, expr):
    body = Body([])
    m = match(in_env(NEWBODY, body, lambda: flatten_expr(expr, Just(destVar))))
    if m('PureExpr(expr) or ImpureExpr(expr)'):
        body.stmts.append(S.Assign(LhsVar(destVar), m.expr))
    elif m('UniqueVar(var)'):
        # flatten_expr may have already written the value for us
        # XXX will this check always be accurate?
        #     ought to have a dedicated ThanksForTheVar() indicator
        if destVar is not m.var:
            body.stmts.append(S.Assign(LhsVar(destVar), m.var))
    return body

def flatten_expr_to_var(expr, optVar):
    m = match(flatten_expr(expr, optVar))
    if m('UniqueVar(var)'):
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
        else:
            undef = Undefined()
            add_extrinsic(TypeOf, undef, extrinsic(TypeOf, expr))
            result = define_temp_var(undef)
        test = gather_expr(m.test)
        trueBlock = store_scope_result(result, m.then)
        falseBlock = store_scope_result(result, m.else_)
        trueCase = CondCase(test, trueBlock)
        falseCase = CondCase(bind_true(), falseBlock)
        set_orig(trueCase, m.then)
        set_orig(falseCase, m.else_)
        cond = S.Cond([trueCase, falseCase])
        set_orig(cond, expr)
        push_newbody(cond)
        return UniqueVar(result)

    elif m('Match(expr, cases)'):
        inVar = flatten_expr_to_var(m.expr, optVar)
        add_extrinsic(Name, inVar, 'in')

        if haveOutVar:
            outVar = fromJust(optVar)
        else:
            outInit = Undefined()
            add_extrinsic(TypeOf, outInit, extrinsic(TypeOf, expr))
            outVar = define_temp_var(outInit)
            add_extrinsic(Name, outVar, 'out')

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
            matchFailure = Body([runtime_void_call('match_fail', [])])
            elseCase = BlockCondCase(Body([]), matchFailure)
            set_orig(elseCase, expr)
            flatCases.append(elseCase)

        cond = BlockCond(flatCases)
        set_orig(cond, expr)
        push_newbody(cond)

        return UniqueVar(outVar)

    elif m('Call(func, args)'):
        target = match(expr.func, "Bind(target)")
        expr.args = map(gather_expr, m.args)
        # type hack
        if matches(target, "Builtin()"):
            return PureExpr(expr)
        # XXX maybe codegen
        if Nullable.isMaybe(target) and len(expr.args) == 0:
            return PureExpr(expr)
        return ImpureExpr(expr)
    elif m('CallIndirect(func, args, _)'):
        # only thing to worry about for expr.func
        # is reassignable function pointers
        assert matches(expr.func, "Bind(_)")
        expr.args = map(gather_expr, m.args)
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
        expr.expr = gather_expr(m.expr)
        return ImpureExpr(expr)
    elif m('TupleLit(vals)'):
        expr.vals = map(gather_expr, m.vals)
        return ImpureExpr(expr)
    elif m('ListLit(vals)'):
        expr.vals = map(gather_expr, m.vals)
        return ImpureExpr(expr)

    elif m('GetEnv(_) or HaveEnv(_)'):
        return ImpureExpr(expr)
    elif m('InEnv(env, init, expr)'):
        push = PushEnv(m.env, gather_expr(m.init))
        set_orig(push, expr)
        push_newbody(push)

        ret = spill(flatten_expr(m.expr, Nothing()))

        pop = PopEnv(m.env)
        set_orig(pop, expr)
        push_newbody(pop)
        return ret

    elif m('GetExtrinsic(_, e) or HasExtrinsic(_, e)'):
        expr.node = gather_expr(m.e)
        return ImpureExpr(expr)
    elif m('ScopeExtrinsic(_, e)'):
        expr.expr = gather_expr(m.e)
        return ImpureExpr(expr)

    else:
        assert False, "Can't deal with %s" % (expr)

def flatten_void_expr(ve):
    m = match(ve)
    if m('VoidCall(Bind(_), args)'):
        ve.args = map(gather_expr, m.args)
        push_newbody(S.VoidStmt(ve))
    elif m('VoidInEnv(env, init, expr)'):
        push = PushEnv(m.env, gather_expr(m.init))
        set_orig(push, ve)
        push_newbody(push)
        flatten_void_expr(m.expr)
        pop = PopEnv(m.env)
        set_orig(pop, ve)
        push_newbody(pop)
    else:
        assert False

def flatten_stmt(stmt):
    m = match(stmt)
    if m('Assign(_, e) or AugAssign(_, _, e)'):
        stmt.expr = gather_expr(m.e)
        push_newbody(stmt)
    elif m('Break() or Continue()'):
        push_newbody(stmt)
    elif m('Cond(cases)'):
        # Turn this into a BlockCond
        newCases = []
        for case in m.cases:
            def go_test():
                test, converse = elide_NOTs(case.test)
                notTest = gather_expr(test if converse else negate(test))
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
        stmt.expr = gather_expr(m.e)
        push_newbody(stmt)
    elif m('Return(e)'):
        stmt.expr = gather_expr(m.e)
        push_newbody(stmt)
    elif m('ReturnNothing()'):
        push_newbody(stmt)

    elif m('While(test, body)'):
        def go():
            assert not matches(m.test, 'Bind(key("False"))'), 'while False?'
            if not matches(m.test, 'Bind(key("True"))'):
                breaker = BreakUnless(gather_expr(m.test))
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
            matchFailure = Body([runtime_void_call('match_fail', [])])
            elseCase = BlockCondCase(Body([]), matchFailure)
            set_orig(elseCase, stmt)
            flatCases.append(elseCase)

        cond = BlockCond(flatCases)
        set_orig(cond, stmt)
        push_newbody(cond)

    elif m('VoidStmt(voidExpr)'):
        flatten_void_expr(m.voidExpr)

    elif m('WriteExtrinsic(_, node, val, _)'):
        stmt.node = gather_expr(m.node)
        stmt.val = gather_expr(m.val)
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
    return S.VoidStmt(VoidCall(bind_var(RUNTIME[name]), args))

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
    for topFunc in unit.funcs:
        topFunc.func.body = flatten_body(topFunc.func.body)
    return build_control_flow(unit)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
