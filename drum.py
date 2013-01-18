from base import *
from atom import *
from quilt import *
import vat

Drum, NoDrum, ArrayDrum = ADT('Drum',
    'NoDrum',
    'ArrayDrum', ('len', int))

Cellar = DT('Cellar', ('localVars', {'*Var': Drum}))
CELLAR = new_env('CELLAR', Cellar)

DrumReplacement = new_extrinsic('DrumReplacement', 'a')

def save(var, drum):
    env(CELLAR).localVars[var] = drum

def recall(var):
    drum = env(CELLAR).localVars.get(var)
    # if unique, should invalidate drum
    return drum if drum is not None else NoDrum()

def obtain(expr):
    m = match(expr)
    if m('Attr(e, field)'):
        _ = obtain(m.e)
        # todo: extract drum from field
        return NoDrum()
    elif m('AttrIx(e)'):
        _ = obtain(m.e)
        return NoDrum()
    elif m('Bind(target)'):
        m2 = match(Bindable.asLocalVar(m.target))
        if m2('Just(local)'):
            return recall(m2.local)
        return NoDrum()

    elif m('Call(Bind(f), args)'):
        drums = map(obtain, m.args)

        if matches(m.f, 'key("rawlen")'):
            assert len(drums) == 1
            m = match(drums[0])
            if m("ArrayDrum(n)"):
                # fill in length from array drum
                arrayLen = L.Lit(IntLit(m.n))
                add_extrinsic(TypeOf, arrayLen, TInt())
                add_extrinsic(DrumReplacement, expr, arrayLen)
        return NoDrum()

    elif m('CallIndirect(_, args, _)'):
        drums = map(obtain, m.args)
        # f's args may consume drums
        return NoDrum()

    elif m('Lit(_) or Undefined() or NullPtr()'):
        return NoDrum()
    elif m('FuncVal(_, _)'):
        return NoDrum()
    elif m('TupleLit(_)'):
        # ought to flatten trivial tuples so that simple swaps etc are handled
        return NoDrum()

    elif m('ListLit(vals)'):
        # oh god what about nested list literals
        return ArrayDrum(len(m.vals))

    elif m('GetEnv(_) or HaveEnv(_)'):
        # will need to restrict env types
        return NoDrum()
    elif m('MakeCtx(_, e)'):
        _ = obtain(m.e)
        return NoDrum()
    elif m('GetExtrinsic(_, _) or HasExtrinsic(_, _)'):
        # will need to restrict extr types
        return NoDrum()
    elif m('ScopeExtrinsic(_, e)'):
        return obtain(m.e)

    assert False, "Can't obtain %s" % (expr,)

def walk_stmt(stmt):
    m = match(stmt)
    if m('Defn(PatVar(var), e) or Assign(LhsVar(var), e)'):
        save(m.var, obtain(m.e))
    elif m('Defn(_, e) or Assign(_, e) or AugAssign(_, _, e)'):
        # todo: destructure tuples at least
        _ = obtain(m.e)
    elif m('VoidStmt(VoidCall(f, args))'):
        drums = map(obtain, m.args)
        # f may consume some drums...
        f = match(m.f, 'Bind(f)')
    elif m('PushEnv(_, e)'):
        _ = obtain(m.e)
    elif m('PopEnv(_)'):
        pass
    elif m('WriteExtrinsic(_, n, v, _)'):
        _ = obtain(m.n)
        _ = obtain(m.v)
    else:
        assert False, "Unexpected %r" % (stmt,)

def walk_flow(pendingBlocks):
    seen = set(pendingBlocks)
    while pendingBlocks:
        block = pendingBlocks.pop(0)
        map_(walk_stmt, block.stmts)

        m = match(block.terminator)
        if m('TermJump(Just(dest))'):
            if m.dest not in seen:
                pendingBlocks.append(m.dest)
                seen.add(m.dest)
        elif m('TermJumpCond(e, Just(true), Just(false))'):
            obtain(m.e)
            if m.true not in seen:
                pendingBlocks.append(m.true)
                seen.add(m.true)
            if m.false not in seen:
                pendingBlocks.append(m.false)
                seen.add(m.false)
        elif m('TermReturnNothing() or TermReturn(_)'):
            pass
        elif m('TermUnreachable()'):
            pass
        else:
            assert False, "Can't deal with: %s" % (block.terminator,)

def walk_func(func):
    cellar = Cellar({})
    in_env(CELLAR, cellar, lambda: walk_flow([func.blocks[0]]))

# Ideally these replacements would be done during the walk
class DrumMutator(vat.Mutator):
    def t_LExpr(self, expr):
        if has_extrinsic(DrumReplacement, expr):
            return extrinsic(DrumReplacement, expr)
        return self.mutate()

def walk_cfg(blockUnit):
    map_(walk_func, blockUnit.funcs)
    vat.mutate(DrumMutator, blockUnit, t_DT(BlockUnit))

def walk(blockUnit):
    scope_extrinsic(DrumReplacement, lambda: walk_cfg(blockUnit))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
