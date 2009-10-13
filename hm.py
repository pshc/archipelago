#!/usr/bin/env python
from atom import *
from base import *
from builtins import *
from types_builtin import *

Env = DT('Env', ('envTable', {Atom: Scheme}), # maps AST nodes to type schemes
                ('envIndex', int),
                ('envRetType', Type),
                ('envReturned', bool),
                ('envPrev', 'Env'))

ENV = None

def fresh():
    global ENV
    i = ENV.envIndex
    ENV.envIndex = i + 1
    return TVar(i)

def unification_failure(e1, e2):
    assert False, "Could not unify %r with %r" % (e1, e2)

def apply_substs_to_scheme(substs, scheme):
    """Modifies in place."""
    ns, t = match(scheme, ("Scheme(vs, t)", tuple2))
    s = substs.copy()
    for n in ns:
        if n in s:
            del s[n]
    scheme.schemeType = apply_substs(s, t)

def apply_substs_to_env(substs, env):
    """Modifies in place."""
    ks = dict_keys(env)
    for k in ks:
        env[k] = apply_substs(substs, env[k])

def apply_substs(substs, t):
    return map_type_vars(lambda n, s: s.get(n, TVar(n)), t, substs)

def compose(s1, s2):
    s3 = s1.copy()
    assert isinstance(s2, dict)
    for k, v in s2.iteritems():
        if k in s1:
            s3 = compose(s3, unify(v, s1[k]))
        s3[k] = apply_substs(s1, v)
    return s3

def free_vars_in_substs(substs):
    fvs = set()
    for k, s in substs.iteritems():
        fvs.update(free_vars(s))
    return fvs

def free_vars_in_tuple(ts):
    # Don't bother with reduce and union for ease of C conversion
    fvs = set()
    for t in ts:
        fvs.update(free_vars(t))
    return fvs

def free_vars_in_func(args, ret):
    fvs = free_vars_in_tuple(args)
    fvs.update(free_vars(ret))
    return fvs

def free_vars(v):
    return match(v, ("TVar(n)", lambda n: set([n])),
                    ("TNullable(t)", free_vars),
                    ("TTuple(ts)", free_vars_in_tuple),
                    ("TFunc(args, ret)", free_vars_in_func),
                    ("_", lambda: set()))

def unify_tuples(t1, list1, t2, list2):
    if len(list1) != len(list2):
        unification_failure(t1, t2)
    s = {}
    for a1, a2 in zip(list1, list2):
        a1 = apply_substs(s, a1)
        a2 = apply_substs(s, a2)
        s = compose(s, unify(a1, a2))
    return s

def unify_funcs(f1, args1, ret1, f2, args2, ret2):
    s = unify_tuples(f1, args1, f2, args2)
    ret1 = apply_substs(s, ret1)
    ret2 = apply_substs(s, ret2)
    return compose(s, unify(ret1, ret2))

def unify_bind(n, e):
    if match(e, ("TVar(n2)", lambda n2: n == n2), ("_", lambda: False)):
        return {}
    if n in free_vars(e):
        unification_failure(TVar(n), e)
    return {n: e}

def unify(e1, e2):
    same = lambda: {}
    fail = lambda: unification_failure(e1, e2)
    return match((e1, e2),
        ("(TVar(n1), _)", lambda n1: unify_bind(n1, e2)),
        ("(_, TVar(n2))", lambda n2: unify_bind(n2, e1)),
        ("(TTuple(t1), TTuple(t2))",
            lambda t1, t2: unify_tuples(e1, t1, e2, t2)),
        ("(TFunc(a1, r1), TFunc(a2, r2))", lambda a1, r1, a2, r2:
            unify_funcs(e1, a1, r1, e2, a2, r2)),
        ("(TInt(), TInt())", same),
        ("(TStr(), TStr())", same),
        ("(TChar(), TChar())", same),
        ("(TBool(), TBool())", same),
        ("(TVoid(), TVoid())", same),
        ("(TTuple(_), TAnyTuple())", same),
        ("(TAnyTuple(), TTuple(_))", same),
        ("(TAnyTuple(), _)", fail),
        ("(_, TAnyTuple())", fail),
        # Not-so-hacky extension
        ("(TNullable(t1), TNullable(t2))", unify),
        ("(_, TNullable(_))", lambda: unify(e2, e1)),
        ("(TNullable(_), TInt())", fail),
        ("(TNullable(_), TChar())", fail),
        ("(TNullable(_), TBool())", fail),
        ("(TNullable(_), TVoid())", fail),
        ("(TNullable(v), t)", unify),
        # Mismatch
        ("_", fail))

def set_type(e, t, substs):
    global ENV
    ENV.envTable[e] = generalize_type(apply_substs(substs, t), substs)

def get_type(e):
    global ENV
    env = ENV
    while e not in env.envTable:
        env = env.envPrev
        assert env is not None, '%s not found in env' % (e,)
    return ENV.envTable[e]

def generalize_type(t, substs):
    gen_vars = free_vars(t).difference(free_vars_in_substs(substs))
    return Scheme(gen_vars, t)

def instantiate_type(scheme):
    vs, t = match(scheme, ("Scheme(vs, t)", tuple2))
    vs_substs = [(v, fresh()) for v in vs]
    return apply_substs(dict(vs_substs), t)

def infer_tuple(ts):
    s = {}
    tupTs = []
    for t in ts:
        tt, s2 = infer_expr(t)
        list_append(tupTs, tt)
        s = compose(s, s2)
    return (TTuple(tupTs), s)

def infer_call(f, args):
    ft, s = infer_expr(f)
    retT = fresh()
    argTs = []
    for a in args:
        at, s2 = infer_expr(a)
        list_append(argTs, at)
        s = compose(s, s2)
    s2 = unify(ft, TFunc(argTs, retT))
    return (retT, compose(s, s2))

def unknown_infer(a):
    assert False, 'Unknown infer case:\n%s' % (a,)

def infer_expr(a):
    return match(a,
        ("Int(_, _)", lambda: (TInt(), {})),
        ("Str(_, _)", lambda: (TStr(), {})),
        ("key('char')", lambda: (TChar(), {})),
        ("key('tuplelit', sized(ts))", infer_tuple),
        ("key('call', cons(f, sized(s)))", infer_call),
        ("Ref(v==key('var'), _, _)",
            lambda v: (get_type(v).schemeType, {})),
        ("Ref(f==key('func'), _, _)",
            lambda f: (instantiate_type(get_type(f)), {})),
        ("Ref(key('symbol', contains(t==key('type'))), _, _)",
            lambda t: (instantiate_type(atoms_to_scheme(t)), {})),
        ("otherwise", unknown_infer))

def infer_DT(dt, cs, vs, nm):
    dtT = fresh() # TODO
    m = dict((v, fresh()) for v in vs)
    for c in cs:
        fieldTs = []
        for f in match(c, ("key('ctor', all(fs, f==key('field')))", identity)):
            t = match(f, ("key('field', contains(key('type', cons(t, _))))",
                          lambda t: atoms_to_type(t, m)))
            list_append(fieldTs, t)
        # This is wrong; should only hold the type in the env,
        # not set it in the atoms
        #set_type(c, TFunc(fieldTs, dtT), {})
    return {}

def infer_assign(a, e):
    newvar = match(a, ("key('var')", lambda: True),
                      ("Ref(key('var'), _, _)", lambda: False))
    t = fresh() if newvar else get_type(a.refAtom).schemeType
    et, substs = infer_expr(e)
    substs = compose(substs, unify(t, et))
    if newvar:
        set_type(a, t, substs)
    return substs

def infer_exprstmt(e):
    t, substs = infer_expr(e)
    return substs

def infer_cond(cases):
    s = {}
    for t, b in cases:
        if match(t, ("key('else')", lambda: False), ("_", lambda: True)):
            tt, ts = infer_expr(t)
            s = compose(ts, s)
            s = compose(unify(tt, TBool()), s)
        s = compose(infer_stmts(b), s)
    return s

def infer_while(test, body):
    tt, s = infer_expr(test)
    s = compose(unify(tt, TBool()), s)
    return compose(infer_stmts(body), s)

def infer_assert(tst, msg):
    tstt, s = infer_expr(tst)
    s = compose(unify(tstt, TBool()), s)
    msgt, s2 = infer_expr(msg)
    s = compose(s2, s)
    return compose(unify(msgt, TStr()), s)

def infer_func(f, args, body):
    global ENV
    # Enter func env
    retT = fresh()
    outerEnv = ENV
    funcEnv = Env({}, outerEnv.envIndex, retT, False, outerEnv)
    ENV = funcEnv
    # Prepare func env
    funcT = fresh()
    set_type(f, funcT, {})
    argTs = [fresh() for arg in args]
    for a, t in zip(args, argTs):
        set_type(a, t, {})
    # Do the stmts
    s = infer_stmts(body)
    # Exit func env
    outerEnv.envIndex = funcEnv.envIndex
    ENV = outerEnv
    # Update our outer env
    if not funcEnv.envReturned:
        retT = TVoid()
    s = compose(unify(funcT, TFunc(argTs, retT)), s)
    set_type(f, funcT, s)
    for a, t in zip(args, argTs):
        set_type(a, t, s)
    return s

def infer_return(e):
    global ENV
    if e is not None:
        t, s = infer_expr(e)
        ENV.envReturned = True
        return compose(unify(ENV.envRetType, t), s)
    return {}

def infer_stmt(a):
    return match(a,
        ("dt==key('DT', all(cs, c==key('ctor'))\
                    and all(vs, v==key('typevar'))) and named(nm)", infer_DT),
        ("key('=', cons(a, cons(e, _)))", infer_assign),
        ("key('exprstmt', cons(e, _))", infer_exprstmt),
        ("key('cond', all(cases, key('case', cons(t, sized(b)))))",infer_cond),
        ("key('while', cons(t, contains(key('body', sized(b)))))",infer_while),
        ("key('assert', cons(t, cons(m, _)))", infer_assert),
        ("f==key('func', contains(key('args', sized(args))) and \
                         contains(key('body', sized(body))))", infer_func),
        ("key('return', cons(e, _))", infer_return),
        ("key('returnnothing')", lambda: infer_return(None)),
        ("otherwise", unknown_infer))

def infer_stmts(ss):
    substs = {}
    for s in ss:
        substs = compose(infer_stmt(s), substs)
    return substs

def infer_types(roots):
    global ENV
    ENV = Env({}, 1, None, False, None)
    substs = infer_stmts(roots)
    for a, t in ENV.envTable.iteritems():
        apply_substs_to_scheme(substs, t)
        a.subs.append(scheme_to_atoms(t))

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short)
    infer_types(short.roots)
    write_mod_repr('hello', short)
    serialize_module(short)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
