from base import *
from atom import *
from quilt import *
import vat

# maybe we should just build entryBlocks later?
Block = DT('Block', ('stmts', ['Stmt(Expr)']),
                    ('terminator', 'Terminator'),
                    ('entryBlocks', ['*Block']))

Terminator, TermJump, TermJumpCond, TermReturnNothing, TermReturn, \
    TermInvalid = ADT('Terminator',
    'TermJump', ('dest', '*Block'),
    'TermJumpCond', ('expr', Expr), ('trueDest', '*Block'),
                    ('falseDest', '*Block'),
    'TermReturnNothing',
    'TermReturn', ('expr', Expr),
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

def empty_block():
    return Block([], TermInvalid(), [])

def ensure_block():
    cfg = env(CFG)
    m = match(cfg.block)
    if m('Just(block)'):
        return m.block
    else:
        block = empty_block()
        cfg.block = Just(block)
        resolve_pending_exits(block)
        return block

def block_push(stmt):
    ensure_block().stmts.append(stmt)

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
        jumps(block, destBlock)

def finish_block(term):
    "Closes up the current block (or makes an empty one) and returns it."
    cfg = env(CFG)
    m = match(cfg.block)
    if m('Just(block)'):
        finished = m.block
        finished.terminator = term
        cfg.pastBlocks.append(finished)
        cfg.block = Nothing()
        return finished
    else:
        new = empty_block()
        resolve_pending_exits(new)
        new.terminator = term
        cfg.pastBlocks.append(new)
        return new

def new_block():
    "Closes up the current block if any, then returns a fresh one."
    new = empty_block()
    cfg = env(CFG)
    m = match(cfg.block)
    if m('Just(block)'):
        old = m.block
        jumps(old, new)
    cfg.block = Just(new)
    resolve_pending_exits(new)
    return new

def exit_to_level(level):
    "Terminates current block, later resolving to the first block at level."
    cfg = env(CFG)
    curLevel = cfg.level
    assert level <= curLevel, "Bad exit to inner level"
    block = finish_block(TermInvalid())
    cfg.pendingExits.setdefault(level, []).append(block)

def exit_to_block(dest):
    "Terminates current block, jumping to the destination block."
    exiting = finish_block(TermJump(dest))
    dest.entryBlocks.append(exiting)

class ControlFlowBuilder(vat.Visitor):
    def TopFunc(self, top):
        blocks = []
        state = ControlFlowState(Nothing(), 0, {}, blocks)
        in_env(CFG, state, lambda: self.visit('func'))
        assert state.level == 0

        if 0 in state.pendingExits:
            pending = state.pendingExits[0]
            returningBlock = Block([], TermReturnNothing(), pending)
            for block in pending:
                block.terminator = TermJump(returningBlock)
            blocks.append(block)

        if len(blocks) == 0:
            blocks.append(Block([], TermReturnNothing(), []))
        bf = BlockFunc(top.var, top.func.params, blocks)
        env(NEWFUNCS).append(bf)

    def FuncExpr(self, fe):
        assert False

    def Body(self, body):
        cfg = env(CFG)
        outerLevel = cfg.level
        innerLevel = outerLevel + 1
        cfg.level = innerLevel
        self.visit()

        if innerLevel in cfg.pendingExits:
            # make an empty block for these pending exits to jump to
            innerPending = cfg.pendingExits[innerLevel]
            del cfg.pendingExits[innerLevel]
            block = new_block()
            for pendingBlock in innerPending:
                jumps(pendingBlock, block)
            # have this one jump to the next level out
            cfg.pendingExits.setdefault(outerLevel, []).append(block)

        cfg.level = outerLevel

    def Break(self, stmt):
        exit_to_level(env(LOOP).level)

    def Cond(self, cond):
        cfg = env(CFG)
        final = empty_block()
        for case in cond.cases:
            if matches(case.test, "Bind(key('True'))"):
                # makeshift else
                vat.visit(ControlFlowBuilder, case.body, 'Body(Expr)')
                exit_to_block(final)
            else:
                true = empty_block()
                nextTest = empty_block()
                test, converse = elide_NOTs(case.test)
                jump = TermJumpCond(test, nextTest, true) if converse else \
                        TermJumpCond(test, true, nextTest)
                _ = finish_block(jump)
                cfg.block = Just(true)
                vat.visit(ControlFlowBuilder, case.body, 'Body(Expr)')
                exit_to_block(final)
                cfg.block = Just(nextTest)

        cfg.block = Just(final)
        resolve_pending_exits(final)

    def Continue(self, stmt):
        exit_to_block(env(LOOP).entryBlock)

    def Return(self, stmt):
        _ = finish_block(TermReturn(stmt.expr))

    def ReturnNothing(self, stmt):
        _ = finish_block(TermReturnNothing())

    def While(self, stmt):
        cfg = env(CFG)
        start = new_block()
        body = new_block()
        def go():
            self.visit('body')
            exit_to_block(start)
        in_env(LOOP, LoopInfo(cfg.level, start), go)
        end = ensure_block()
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


def build_control_flow(unit):
    funcs = []
    t = t_DT(ExpandedUnit)
    in_env(NEWFUNCS, funcs, lambda: vat.visit(ControlFlowBuilder, unit, t))

    for func in funcs:
        print 'made', extrinsic(Name, func.var)
        for block in func.blocks:
            print 'BLOCK'
            for stmt in block.stmts:
                print '   ', stmt
            print ' >>', match(block.terminator,
                ('TermJump(d)', lambda d: 'jump'),
                ('TermJumpCond(c, _, _)', lambda c: '?: %r' % (c,)),
                ('TermReturnNothing()', lambda: 'ret void'),
                ('TermReturn(e)', lambda e: 'ret %r' % (e,)))


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
        push_newbody(S.Cond([then]))

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
        push_newbody(S.Cond([then]))

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
        push_newbody(S.Cond([CondCase(test, trueBlock),
                          CondCase(true(), falseBlock)]))
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
