#!/usr/bin/env python
from atom import *
from base import *
from builtins import *
from types_builtin import *

OmniEnv = DT('OmniEnv', ('omniTypeAugs', {Atom: Scheme}),
                        ('omniFieldDTs', {Atom: Atom}))

Env = DT('Env', ('envTable', {Atom: Scheme}),
                ('envRetType', Type),
                ('envReturned', bool),
                ('envPrev', 'Env'))

GlobalEnv = DT('GlobalEnv', ('omniEnv', OmniEnv),
                            ('curEnv', Env))

ENV = None

def fresh():
    return TMeta(TypeCell(None))

def unification_failure(e1, e2, msg):
    assert False, "Could not unify %r with %r: %s" % (e1, e2, msg)

def unify_tuples(t1, list1, t2, list2, desc):
    if len(list1) != len(list2):
        unification_failure(t1, t2, "%s length mismatch" % (desc,))
    for a1, a2 in zip(list1, list2):
        unify(a1, a2)

def unify_funcs(f1, args1, ret1, f2, args2, ret2):
    unify_tuples(f1, args1, f2, args2, "func params")
    unify(ret1, ret2)

def unify_metas(t1, t2):
    c1 = t1.metaCell
    c2 = t2.metaCell
    if c1.cellType is None:
        if c2.cellType is None:
            c1.cellType = TMeta(c2)
        else:
            c1.cellType = c2.cellType
        #t1.metaCell = c2
    elif c2.cellType is None:
        c2.cellType = c1.cellType
        #t2.metaCell = c1
    else:
        unify(c1.cellType, c2.cellType)

def unify_bind_meta(meta, t):
    cell = meta.metaCell
    if cell.cellType is None:
        cell.cellType = t
    else:
        unify(cell.cellType, t)

# XXX: NULL MUST DIE
def unify_nullable(n, e):
    fail = lambda m: lambda: unification_failure(TNullable(n), e,
                                                 "%s not nullable" % (m,))
    match(e,
        ("TInt()", fail("unboxed int")),
        ("TChar()", fail("unboxed char")),
        ("TBool()", fail("unboxed bool")),
        ("TVoid()", fail("void return")),
        ("_", lambda: unify(n, e)))

def unify(e1, e2):
    global ENV
    same = lambda: None
    fail = lambda m: lambda: unification_failure(e1, e2, m)
    match((e1, e2),
        ("(TMeta(_), TMeta(_))", lambda: unify_metas(e1, e2)),
        ("(TMeta(_), _)", lambda: unify_bind_meta(e1, e2)),
        ("(_, TMeta(_))", lambda: unify_bind_meta(e2, e1)),
        ("(TVar(v1), TVar(v2))", lambda v1, v2: same() if v1 is v2
                                 else fail("mismatched type vars")),
        ("(TTuple(t1), TTuple(t2))",
            lambda t1, t2: unify_tuples(e1, t1, e2, t2, "tuple")),
        ("(TFunc(a1, r1), TFunc(a2, r2))", lambda a1, r1, a2, r2:
            unify_funcs(e1, a1, r1, e2, a2, r2)),
        ("(TData(a), TData(b))", lambda a, b: same() if a is b
                                 else fail("mismatched datatypes")()),
        ("(TInt(), TInt())", same),
        ("(TStr(), TStr())", same),
        ("(TChar(), TChar())", same),
        ("(TBool(), TBool())", same),
        ("(TVoid(), TVoid())", same),
        ("(TTuple(_), TAnyTuple())", same),
        ("(TAnyTuple(), TTuple(_))", same),
        ("(TAnyTuple(), _)", fail("tuple expected")),
        ("(_, TAnyTuple())", fail("tuple expected")),
        ("(TNullable(t1), TNullable(t2))", unify),
        ("(TNullable(v), _)", lambda v: unify_nullable(v, e2)),
        ("(_, TNullable(v))", lambda v: unify_nullable(v, e1)),
        ("_", fail("type mismatch")))

def set_scheme(e, s, augment_ast):
    global ENV
    env = ENV.curEnv
    while env is not None:
        assert e not in env.envTable, "%s already has a type" % (e,)
        env = env.envPrev
    ENV.curEnv.envTable[e] = (s, augment_ast)

def set_monotype(e, t, augment_ast):
    set_scheme(e, Scheme([], t), augment_ast)

def get_scheme(e):
    global ENV
    env = ENV.curEnv
    while env is not None:
        if e in env.envTable:
            s, aug = env.envTable[e]
            return s
        env = env.envPrev
    assert False, '%s not in scope' % (e,)

def in_new_env(f):
    global ENV
    outerEnv = ENV.curEnv
    ENV.curEnv = Env({}, None, False, outerEnv)

    ret = f()

    # Save augmentations from that env
    for e, info in ENV.curEnv.envTable.iteritems():
        s, aug = info
        if aug:
            ENV.omniEnv.omniTypeAugs[e] = s

    ENV.curEnv = outerEnv
    return ret

def instantiate_scheme(s):
    vs, t = match(s, ('Scheme(vs, t)', tuple2))
    repl = dict((v, fresh()) for v in vs)
    if len(vs) > 0:
        t = map_type_vars(lambda v: repl.get(v.varAtom, v), t)
    return t

def generalize_type(t, polyEnv):
    metas = free_meta_vars(t)
    while polyEnv is not None:
        for envT in polyEnv.envTable:
            metas = metas.difference(free_meta_vars(envT))
        polyEnv = polyEnv.envPrev
    tvs = []
    for i, meta in enumerate(metas):
        tv = symref('typevar', [symname(chr(97 + i))])
        meta.metaCell.cellType = TVar(tv)
        list_append(tvs, tv)
    return Scheme(tvs, t)

def get_type(e):
    return instantiate_scheme(get_scheme(e))

def free_tuple_meta_vars(ts):
    return reduce(lambda s, t: s.union(free_meta_vars(t)), ts, set())

def free_func_meta_vars(args, ret):
    return free_tuple_meta_vars(args).union(free_meta_vars(ret))

def free_meta_vars(t):
    return match(t, ('v==TMeta(TypeCell(r))',
                       lambda v, r: set([v]) if r is None
                                             else free_meta_vars(r)),
                    ('TNullable(t)', free_meta_vars),
                    ('TTuple(ts)', free_tuple_meta_vars),
                    ('TFunc(args, ret)', free_func_meta_vars),
                    ('_', lambda: set()))

def check_tuple(et, ts):
    unify(et, TTuple(map(infer_expr, ts)))

def decompose_func_type(ft, nargs):
    argTs, retT = match(ft, ("TFunc(argTs, retT)", tuple2),
                            ("_", lambda: ([], None)))
    if retT is None:
        argTs = [fresh() for n in range(nargs)]
        retT = fresh()
        unify(ft, TFunc(argTs, retT))
    assert len(argTs) == nargs
    return (argTs, retT)

def check_call(et, f, args):
    argTs, retT = decompose_func_type(infer_expr(f), len(args))
    for argT, arg in zip(argTs, args):
        check_expr(argT, arg)
    unify(retT, et)

def check_lambda(tv, lam, args, e):
    body = [symref('return', [e])] # stupid hack
    s = infer_func_scheme(None, args, body) # non-recursive, so None
    set_scheme(lam, s, True)
    t = instantiate_scheme(s) # stupider hack
    unify(tv, t)

def pat_var(tv, v):
    set_monotype(v, tv, True)

def pat_capture(tv, v, p):
    pat_var(tv, v)
    check_pat(tv, p)

# XXX: Instantiation has to be consistent across all match cases...
def pat_ctor(tv, ctor, args):
    ctorT = instantiate_scheme(get_scheme(ctor))
    fieldTs, dt = match(ctorT, ("TFunc(fs, dt)", tuple2))
    unify(tv, dt)
    assert len(args) == len(fieldTs), "Wrong ctor param count"
    for arg, fieldT in zip(args, fieldTs):
        check_pat(fieldT, arg)

def check_pat(tv, p):
    match(p,
        ("Int(_, _)", lambda: unify(tv, TInt())),
        ("Str(_, _)", lambda: unify(tv, TStr())),
        ("key('wildcard')", lambda: None),
        ("key('tuplelit', sized(ps))",
            lambda ps: unify(tv, TTuple(map(infer_pat, ps)))),
        ("v==key('var')", lambda v: pat_var(tv, v)),
        ("key('capture', cons(v, cons(p, _)))",
            lambda v, p: pat_capture(tv, v, p)),
        ("key('ctor', cons(Ref(c, _, _), sized(args)))",
            lambda c, args: pat_ctor(tv, c, args)),
        )

def infer_pat(p):
    tv = fresh()
    check_pat(tv, p)
    return tv

def check_match(retT, m, e, cs):
    et = infer_expr(e)
    for c in cs:
        cp, ce = match(c, ("key('case', cons(p, cons(e, _)))", tuple2))
        def check_case():
            check_pat(et, cp)
            check_expr(retT, ce)
        in_new_env(check_case)
    # Help out C transmogrification with some extra type annotations
    set_monotype(m, retT, True)
    set_monotype(e, et, True)

def check_attr(et, struct, a):
    global ENV
    unify(ENV.omniEnv.omniFieldDTs[a], infer_expr(struct))
    unify(et, get_type(a))

def unknown_infer(a):
    assert False, 'Unknown infer case:\n%s' % (a,)

def check_binding(tv, b):
    unify(tv, get_type(b))

def check_builtin(tv, s):
    unify(tv, instantiate_scheme(atoms_to_scheme(s)))

def check_expr(tv, e):
    """Algorithm M."""
    match(e,
        ("Int(_, _)", lambda: unify(tv, TInt())),
        ("Str(_, _)", lambda: unify(tv, TStr())),
        ("key('char')", lambda: unify(tv, TChar())),
        ("key('tuplelit', sized(ts))", lambda ts: check_tuple(tv, ts)),
        ("key('call', cons(f, sized(s)))", lambda f, s: check_call(tv, f, s)),
        ("l==key('lambda', sized(args, cons(e, _)))",
            lambda l, a, e: check_lambda(tv, l, a, e)),
        ("m==key('match', cons(p, all(cs, c==key('case'))))",
            lambda m, p, cs: check_match(tv, m, p, cs)),
        ("key('attr', cons(s, cons(Ref(a, _, _), _)))",
            lambda s, a: check_attr(tv, s, a)),
        ("Ref(v==key('var'), _, _)",
            lambda v: check_binding(tv, v)),
        ("Ref(f==key('func' or 'ctor'), _, _)",
            lambda f: check_binding(tv, f)),
        ("Ref(key('symbol', contains(s==key('type'))), _, _)",
            lambda s: check_builtin(tv, s)),
        ("_", lambda: unknown_infer(e)))

def infer_expr(e):
    tv = fresh()
    check_expr(tv, e)
    return tv

def infer_DT(dt, cs, vs, nm):
    dtT = TData(dt)
    tvs = match(dt, ("key('DT', all(tvs, tv==key('typevar')))", identity))
    for c in cs:
        fieldTs = []
        for f in match(c, ("key('ctor', all(fs, f==key('field')))", identity)):
            t = match(f, ("key('field', contains(key('type', cons(t, _))))",
                          lambda t: atoms_to_type(t)))
            list_append(fieldTs, t)
            set_monotype(f, t, False)
        funcT = TFunc(fieldTs, dtT)
        # TODO: Should use only the typevars that appear in this ctor
        set_scheme(c, Scheme(tvs, funcT), False)

def infer_assign(a, e):
    newvar = match(a, ("key('var')", lambda: True),
                      ("Ref(key('var'), _, _)", lambda: False))
    t = fresh() if newvar else get_type(a.refAtom)
    check_expr(t, e)
    if newvar:
        global ENV
        set_scheme(a, generalize_type(t, ENV.curEnv), True)

def infer_exprstmt(e):
    t = infer_expr(e)

def infer_cond(subs, cases):
    for t, b in cases:
        check_expr(TBool(), t)
        infer_stmts(b)
    else_ = match(subs, ('contains(key("else", sized(body)))', identity),
                        ('_', lambda: None))
    if else_ is not None:
        infer_stmts(else_)

def infer_while(test, body):
    check_expr(TBool(), test)
    infer_stmts(body)

def infer_assert(tst, msg):
    check_expr(TBool(), tst)
    check_expr(TStr(), msg)

def infer_func_scheme(f, args, body):
    def inside_func_env():
        global ENV
        env = ENV.curEnv

        retT = fresh()
        env.envRetType = retT
        funcT = fresh()
        if f is not None:
            set_monotype(f, funcT, False)
        argTs = []
        for a in args:
            t = fresh()
            set_monotype(a, t, False)
            list_append(argTs, t)

        infer_stmts(body)

        if not env.envReturned:
            unify(retT, TVoid())
        unify(funcT, TFunc(argTs, retT))
        return generalize_type(funcT, env)
    return in_new_env(inside_func_env)

def infer_func(f, args, body):
    set_scheme(f, infer_func_scheme(f, args, body), True)

def infer_return(e):
    global ENV
    if e is not None:
        check_expr(ENV.curEnv.envRetType, e)
        ENV.curEnv.envReturned = True

def infer_stmt(a):
    match(a,
        ("dt==key('DT', all(cs, c==key('ctor'))\
                    and all(vs, v==key('typevar'))) and named(nm)", infer_DT),
        ("key('=', cons(a, cons(e, _)))", infer_assign),
        ("key('exprstmt', cons(e, _))", infer_exprstmt),
        ("key('cond', subs and all(cases, key('case', cons(t, sized(b)))))",
            infer_cond),
        ("key('while', cons(t, contains(key('body', sized(b)))))",infer_while),
        ("key('assert', cons(t, cons(m, _)))", infer_assert),
        ("f==key('func', contains(key('args', sized(args))) and \
                         contains(key('body', sized(body))))", infer_func),
        ("key('return', cons(e, _))", infer_return),
        ("key('returnnothing')", lambda: infer_return(None)),
        ("otherwise", unknown_infer))

def infer_stmts(ss):
    for s in ss:
        infer_stmt(s)

def setup_infer_env(roots):
    fields = {}
    for dt in roots:
        cs = match(dt, ("key('DT', all(cs, c==key('ctor')))", identity),
                       ("_", lambda: []))
        dtT = TData(dt)
        for c in cs:
            fs = match(c, ("key('ctor', all(fs, f==key('field')))", identity))
            for f in fs:
                fields[f] = dtT
    omni = OmniEnv({}, fields)
    return GlobalEnv(omni, None)

def infer_types(roots):
    global ENV
    ENV = setup_infer_env(roots)
    in_new_env(lambda: infer_stmts(roots))
    for e, s in ENV.omniEnv.omniTypeAugs.iteritems():
        e.subs.append(scheme_to_atoms(s))

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short)
    infer_types(short.roots)
    write_mod_repr('hello', short)
    serialize_module(short)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
