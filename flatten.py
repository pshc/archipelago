from base import *
from atom import *
from quilt import *
import vat

# maybe we should just build entryBlocks later?
Block = DT('Block', ('label', str),
                    ('stmts', ['Stmt(Expr)']),
                    ('terminator', 'Terminator'),
                    ('entryBlocks', ['*Block']))

Terminator, TermJump, TermJumpCond, TermReturnNothing, TermReturn, \
    TermUnreachable, TermInvalid = ADT('Terminator',
    'TermJump', ('dest', '*Block'),
    'TermJumpCond', ('expr', Expr), ('trueDest', '*Block'),
                    ('falseDest', '*Block'),
    'TermReturnNothing',
    'TermReturn', ('expr', Expr),
    'TermUnreachable',
    'TermInvalid')

ControlFlowState = DT('ControlFlowState',
        ('block', 'Maybe(Block)'),
        ('level', int),
        ('pendingExits', {int: ['*Block']}),
        ('pastBlocks', [Block]))

CFG = new_env('CFG', ControlFlowState)

LoopInfo = DT('LoopInfo', ('level', int), ('entryBlock', '*Block'))

LOOP = new_env('LOOP', int)

BlockFunc = DT('BlockFunc', ('var', Var),
                            ('params', [Var]),
                            ('blocks', [Block]))

NEWFUNCS = new_env('NEWFUNCS', [BlockFunc])

def empty_block(label, index):
    label = '%s.%d' % (label, index)
    return Block(label, [], TermInvalid(), [])

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
    assert matches(src.terminator, 'TermInvalid()')
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

def orig_index(stmt):
    return vat.orig_loc(stmt).index

class ControlFlowBuilder(vat.Visitor):
    def TopFunc(self, top):
        blocks = []
        state = ControlFlowState(Just(empty_block('', 0)), 0, {}, blocks)
        in_env(CFG, state, lambda: self.visit('func'))
        assert state.level == 0
        assert 0 not in state.pendingExits
        if isJust(state.block):
            last = fromJust(state.block)
            last.terminator = TermReturnNothing()
            blocks.append(last)
        elif len(blocks) == 0:
            b = empty_block('', 0)
            b.terminator = TermReturnNothing()
            blocks.append(b)
        bf = BlockFunc(top.var, top.func.params, blocks)
        env(NEWFUNCS).append(bf)

    def FuncExpr(self, fe):
        assert False, "FuncExprs ought to be gone"

    def Body(self, body):
        cfg = env(CFG)
        outer = cfg.level
        inner = outer + 1

        cfg.level = inner
        self.visit()
        assert inner not in cfg.pendingExits, "Dangling exit?"
        cfg.level = outer

    def Break(self, stmt):
        exit_to_level(env(LOOP).level)

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
                vat.visit(ControlFlowBuilder, case.body, 'Body(Expr)')
                exit_to_level(exitLevel)
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
            vat.visit(ControlFlowBuilder, case.body, 'Body(Expr)')
            exit_to_level(exitLevel)
            if not isLast:
                cfg.block = Just(nextTest)

        if exitLevel in cfg.pendingExits:
            _ = start_new_block('endif', orig_index(cond))

    def Continue(self, stmt):
        finish_jump(env(LOOP).entryBlock)

    def Return(self, stmt):
        finish_block(TermReturn(stmt.expr))

    def ReturnNothing(self, stmt):
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
    def VoidStmt(self, stmt):
        block_push(stmt)
        m = match(stmt.voidExpr)
        if m('VoidCall(Bind(f), _)'):
            if matches(extrinsic(TypeOf, m.f), 'TFunc(_, Bottom(), _)'):
                finish_block(TermUnreachable())
    # ugh what is this doing here
    def WriteExtrinsic(self, stmt):
        block_push(stmt)

    def t_Stmt(self, stmt):
        assert False, "Can't deal with %s" % stmt

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
            assert entryCounts[block] == n, "Bad entry count to %s" % (lbl,)

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
    return funcs

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
        falseCase = CondCase(true(), falseBlock)
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

def true():
    bind = L.Bind(BUILTINS['True'])
    add_extrinsic(TypeOf, bind, TBool())
    return bind

def flatten_unit(unit):
    vat.mutate(CompoundFlattener, unit, t_DT(ExpandedUnit))
    return build_control_flow(unit)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
