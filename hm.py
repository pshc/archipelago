#!/usr/bin/env python
from atom import *
from base import *
from builtins import *
from types_builtin import *

OmniEnv = DT('OmniEnv', ('omniTypeAugs', {Atom: Type}),
                        ('omniFieldDTs', {Atom: Atom}))

Env = DT('Env', ('envTable', {Atom: Type}),
                ('envRetType', Type),
                ('envReturned', bool),
                ('envPrev', 'Env'))

GlobalEnv = DT('GlobalEnv', ('omniEnv', OmniEnv),
                            ('curEnv', Env))

ENV = None

def fresh():
    return TVar(TypeCell(None))

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

def unify_tvars(t1, t2):
    c1 = t1.varCell
    c2 = t2.varCell
    if c1.cellType is None:
        if c2.cellType is None:
            c1.cellType = TVar(c2)
        else:
            c1.cellType = c2.cellType
        #t1.varCell = c2
    elif c2.cellType is None:
        c2.cellType = c1.cellType
        #t2.varCell = c1
    else:
        unify(c1.cellType, c2.cellType)

def unify_bind(tvar, t):
    cell = tvar.varCell
    if cell.cellType is None:
        cell.cellType = t
    else:
        unify(cell.cellType, t)

def unify(e1, e2):
    global ENV
    same = lambda: None
    fail = lambda m: lambda: unification_failure(e1, e2, m)
    match((e1, e2),
        ("(TVar(_), TVar(_))", lambda: unify_tvars(e1, e2)),
        ("(TVar(_), _)", lambda: unify_bind(e1, e2)),
        ("(_, TVar(_))", lambda: unify_bind(e2, e1)),
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
        # XXX: NULL MUST DIE
        ("(TNullable(t1), TNullable(t2))", unify),
        ("(_, TNullable(_))", lambda: unify(e2, e1)),
        ("(TNullable(_), TInt())", fail("unboxed int not nullable")),
        ("(TNullable(_), TChar())", fail("unboxed char not nullable")),
        ("(TNullable(_), TBool())", fail("unboxed bool not nullable")),
        ("(TNullable(_), TVoid())", fail("void return not nullable")),
        ("(TNullable(v), t)", unify),
        # Mismatch
        ("_", fail("type mismatch")))

def set_type(e, t, augment_ast):
    global ENV
    env = ENV.curEnv
    while env is not None:
        assert e not in env.envTable, "%s already has a type" % (e,)
        env = env.envPrev
    ENV.curEnv.envTable[e] = (t, augment_ast)

def get_type(e):
    global ENV
    env = ENV.curEnv
    while env is not None:
        if e in env.envTable:
            t, aug = env.envTable[e]
            return t
        env = env.envPrev
    assert False, '%s not in scope' % (e,)

def in_new_env(f):
    global ENV
    outerEnv = ENV.curEnv
    ENV.curEnv = Env({}, None, False, outerEnv)

    ret = f()

    # Save augmentations from that env
    for e, info in ENV.curEnv.envTable.iteritems():
        t, aug = info
        if aug:
            ENV.omniEnv.omniTypeAugs[e] = t

    ENV.curEnv = outerEnv
    return ret

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

def pat_var(tv, v):
    set_type(v, tv, True)

def pat_capture(tv, v, p):
    pat_var(tv, v)
    check_pat(tv, p)

def pat_ctor(tv, ctor_ref, ctor, args):
    fieldTs, dt = match(get_type(ctor), ("TFunc(fs, dt)", tuple2))
    unify(tv, dt)
    argTs = map(infer_pat, args)
    unify_tuples(ctor_ref, argTs, ctor, fieldTs, "ctor params")

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
        ("r==key('ctor', cons(Ref(c, _, _), sized(args)))",
            lambda r, c, args: pat_ctor(tv, r, c, args)),
        )

def infer_pat(p):
    tv = fresh()
    check_pat(tv, p)
    return tv

def check_match(retT, m, e, cs):
    et = infer_expr(e)
    for c in cs:
        cp, ce = match(c, ("key('case', cons(p, cons(e, _)))", tuple2))
        def check_case(env):
            check_pat(et, cp)
            check_expr(retT, ce)
        in_new_env(check_case)
    # Help out C transmogrification with some extra type annotations
    set_type(m, retT, True)
    set_type(e, et, True)

def check_attr(et, struct, a):
    global ENV
    unify(ENV.omniEnv.omniFieldDTs[a], infer_expr(struct))
    unify(et, get_type(a))

def unknown_infer(a):
    assert False, 'Unknown infer case:\n%s' % (a,)

def check_expr(tv, e):
    """Algorithm M."""
    match(e,
        ("Int(_, _)", lambda: unify(tv, TInt())),
        ("Str(_, _)", lambda: unify(tv, TStr())),
        ("key('char')", lambda: unify(tv, TChar())),
        ("key('tuplelit', sized(ts))", lambda ts: check_tuple(tv, ts)),
        ("key('call', cons(f, sized(s)))", lambda f, s: check_call(tv, f, s)),
        ("m==key('match', cons(p, all(cs, c==key('case'))))",
            lambda m, p, cs: check_match(tv, m, p, cs)),
        ("key('attr', cons(s, cons(Ref(a, _, _), _)))",
            lambda s, a: check_attr(tv, s, a)),
        ("Ref(v==key('var'), _, _)",
            lambda v: unify(tv, get_type(v))),
        ("Ref(f==key('func' or 'ctor'), _, _)",
            lambda f: unify(tv, get_type(f))),
        ("Ref(key('symbol', contains(key('type', cons(t, _)))), _, _)",
            lambda t: unify(tv, atoms_to_type(t))),
        ("_", lambda: unknown_infer(e)))

def infer_expr(e):
    tv = fresh()
    check_expr(tv, e)
    return tv

def infer_DT(dt, cs, vs, nm):
    dtT = TData(dt)
    for c in cs:
        fieldTs = []
        for f in match(c, ("key('ctor', all(fs, f==key('field')))", identity)):
            t = match(f, ("key('field', contains(key('type', cons(t, _))))",
                          lambda t: atoms_to_type(t)))
            list_append(fieldTs, t)
            set_type(f, t, False)
        funcT = TFunc(fieldTs, dtT)
        set_type(c, funcT, False)

def infer_assign(a, e):
    newvar = match(a, ("key('var')", lambda: True),
                      ("Ref(key('var'), _, _)", lambda: False))
    t = fresh() if newvar else get_type(a.refAtom)
    check_expr(t, e)
    if newvar:
        set_type(a, t, True)

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

def infer_func(f, args, body):
    def inside_func_env():
        global ENV
        env = ENV.curEnv

        retT = fresh()
        env.envRetType = retT
        funcT = fresh()
        set_type(f, funcT, False)
        argTs = []
        for a in args:
            t = fresh()
            set_type(a, t, False)
            list_append(argTs, t)

        infer_stmts(body)

        if not env.envReturned:
            unify(retT, TVoid())
        unify(funcT, TFunc(argTs, retT))
        return funcT
    set_type(f, in_new_env(inside_func_env), True)

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
    for e, t in ENV.omniEnv.omniTypeAugs.iteritems():
        e.subs.append(symref('type', [type_to_atoms(t)]))

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short)
    infer_types(short.roots)
    write_mod_repr('hello', short)
    serialize_module(short)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
