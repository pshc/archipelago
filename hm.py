#!/usr/bin/env python
from atom import *
from base import *
from builtins import *
from types_builtin import *

Env = DT('Env', ('envTable', {Atom: Scheme}), # maps AST nodes to type schemes
                ('envIndex', int),
                ('envRetTypes', [(Type, bool)]))

def fresh(env):
    i = env.envIndex
    env.envIndex = i + 1
    return TVar(i)

def unification_failure(e1, e2, env):
    assert False, "Could not unify %r with %r" % (e1, e2)

def apply_substs_to_scheme(substs, scheme):
    """Modifies in place."""
    vs, t = match(scheme, ("Scheme(vs, t)", tuple2))
    s = substs.copy()
    #for v in vs:
    #    if v in s:
    #        del s[v]
    scheme.schemeType = apply_substs(s, t)

def apply_substs_to_env(substs, env):
    """Modifies in place."""
    ks = dict_keys(env)
    for k in ks:
        env[k] = apply_substs(substs, env[k])

def _apply_to_var(t, s):
    """Ugh."""
    for k, v in s.iteritems():
        if k is t or match((k, t), ("(TVar(a), TVar(b))", lambda a, b: a == b),
                                   ("_", lambda: False)):
            return v
    return t

def apply_substs(substs, t):
    return map_type_vars(_apply_to_var, t, substs)

def compose_substs(s1, s2):
    s3 = s1.copy()
    if not isinstance(s2, dict):
        assert False
    for k, v in s2.iteritems():
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
    return match(v, ("TVar(_)", lambda: set([v])),
                    ("TTuple(ts)", free_vars_in_tuple),
                    ("TFunc(args, ret)", free_vars_in_func),
                    ("_", lambda: set()))

def unify_tuples(t1, list1, t2, list2, env):
    if len(list1) != len(list2):
        unification_failure(t1, t2, env)
    s = {}
    for a1, a2 in zip(list1, list2):
        a1 = apply_substs(s, a1)
        a2 = apply_substs(s, a2)
        s = compose_substs(s, unify(a1, a2, env))
    return s

def unify_funcs(f1, args1, ret1, f2, args2, ret2, env):
    s = unify_tuples(f1, args1, f2, args2, env)
    ret1 = apply_substs(s, ret1)
    ret2 = apply_substs(s, ret2)
    return compose_substs(s, unify(ret1, ret2, env))

def unify_bind(v, e, env):
    if is_typevar(e) and typevars_equal(v, e):
        return {}
    if v in free_vars(e):
        unification_failure(v, e, env)
    return {v: e}

def unify(e1, e2, env):
    same = lambda: {}
    fail = lambda: unification_failure(e1, e2, env)
    return match((e1, e2),
        ("(TVar(_), _)", lambda: unify_bind(e1, e2, env)),
        ("(_, TVar(_))", lambda: unify_bind(e2, e1, env)),
        ("(TTuple(t1), TTuple(t2))",
            lambda t1, t2: unify_tuples(e1, t1, e2, t2, env)),
        ("(TFunc(a1, r1), TFunc(a2, r2))", lambda a1, r1, a2, r2:
            unify_funcs(e1, a1, r1, e2, a2, r2, env)),
        ("(TInt(), TInt())", same),
        ("(TStr(), TStr())", same),
        ("(TChar(), TChar())", same),
        ("(TBool(), TBool())", same),
        ("(TVoid(), TVoid())", same),
        # XXX: Hacky extension
        ("(TTuple(_), TAnyTuple())", same),
        ("(TAnyTuple(), TTuple(_))", same),
        ("(TAnyTuple(), _)", fail),
        ("(_, TAnyTuple())", fail),
        # Not-so-hacky extension
        ("(TNullable(), TNullable())", same),
        ("(_, TNullable())", lambda: unify(e2, e1, env)),
        ("(TNullable(), TInt())", fail),
        ("(TNullable(), TChar())", fail),
        ("(TNullable(), TBool())", fail),
        ("(TNullable(), TVoid())", fail),
        ("(TNullable(), _)", lambda: {e1: e2}),
        # Mismatch
        ("_", fail))

def set_type(e, t, env, substs):
    env.envTable[e] = generalize_type(apply_substs(substs, t), substs)

def get_type(e, env):
    return instantiate_type(env.envTable[e], env)

def generalize_type(t, substs):
    gen_vars = free_vars(t).difference(free_vars_in_substs(substs))
    return Scheme(gen_vars, t)

def instantiate_type(scheme, env):
    vs, t = match(scheme, ("Scheme(vs, t)", tuple2))
    return t
    #vs_substs = [(v, fresh(env)) for v in vs]
    #return apply_substs(dict(vs_substs), t)

def infer_tuple(ts, env):
    s = {}
    tupTs = []
    for t in ts:
        tt, s2 = infer_expr(t, env)
        list_append(tupTs, tt)
        s = compose_substs(s, s2)
    return (TTuple(tupTs), s)

def infer_call(f, args, env):
    ft, s = infer_expr(f, env)
    retT = fresh(env)
    argTs = []
    for a in args:
        at, s2 = infer_expr(a, env)
        list_append(argTs, at)
        s = compose_substs(s, s2)
    s2 = unify(ft, TFunc(argTs, retT), env)
    return (retT, compose_substs(s, s2))

def unknown_infer(a, env):
    assert False, 'Unknown infer_expr case:\n%s' % (a,)

def infer_expr(a, env):
    return match(a,
        ("Int(_, _)", lambda: (TInt(), {})),
        ("Str(_, _)", lambda: (TStr(), {})),
        ("key('char')", lambda: (TChar(), {})),
        ("key('tuplelit', sized(ts))", lambda ts: infer_tuple(ts, env)),
        ("key('call', cons(f, sized(s)))", lambda f, s: infer_call(f, s, env)),
        ("Ref(v==key('var' or 'func'), _, _)",
            lambda v: (get_type(v, env), {})),
        ("Ref(key('symbol', contains(t==key('type'))), _, _)",
            lambda t: (instantiate_type(atoms_to_scheme(t), env), {})),
        ("otherwise", lambda e: unknown_infer(e, env)))

def infer_DT(fs, nm, env):
    print 'DT', nm
    return {}

def infer_assign(a, e, env):
    newvar = match(a, ("key('var')", lambda: True),
                      ("Ref(key('var'), _, _)", lambda: False))
    t = fresh(env) if newvar else get_type(a.refAtom, env)
    et, substs = infer_expr(e, env)
    substs = compose_substs(substs, unify(t, et, env))
    if newvar:
        set_type(a, t, env, substs)
    return substs

def infer_exprstmt(e, env):
    t, substs = infer_expr(e, env)
    return substs

def infer_cond(cases, env):
    s = {}
    for t, b in cases:
        if match(t, ("key('else')", lambda: False), ("_", lambda: True)):
            tt, ts = infer_expr(t, env)
            s = compose_substs(ts, s)
            s = compose_substs(unify(tt, TBool(), env), s)
        s = compose_substs(infer_stmts(b, env), s)
    return s

def infer_assert(tst, msg, env):
    tstt, s = infer_expr(tst, env)
    s = compose_substs(unify(tstt, TBool(), env), s)
    msgt, s2 = infer_expr(msg, env)
    s = compose_substs(s2, s)
    return compose_substs(unify(msgt, TStr(), env), s)

def infer_func(f, args, body, env):
    #argTs = [Scheme([], fresh(env)) for arg in args]
    argTs = [fresh(env) for arg in args]
    for a, t in zip(args, argTs):
        set_type(a, t, env, {})
    retT = fresh(env)
    set_type(f, TFunc(argTs, retT), env, {})
    # Push ret type so that "return"s in the body can be unified
    list_prepend(env.envRetTypes, (retT, False))
    s = infer_stmts(body, env)
    (rt, returned) = list_pop_front(env.envRetTypes)
    if not returned:
        s = compose_substs(unify(retT, TVoid(), env), s)
    return s

def infer_return(e, env):
    retT, returned = list_head(env.envRetTypes)
    if e is not None:
        t, s = infer_expr(e, env)
        if not returned:
            # Record that some value was returned in this function
            list_pop_front(env.envRetTypes)
            list_prepend(env.envRetTypes, (retT, True))
        return compose_substs(unify(retT, t, env), s)
    return {}

def infer_stmt(a, env):
    return match(a,
        ("key('DT', all(fs, key('field') and named(fnm)))"
            " and named(nm)", lambda fs, nm: infer_DT(fs, nm, env)),
        ("key('=', cons(a, cons(e, _)))", lambda a, e: infer_assign(a,e,env)),
        ("key('exprstmt', cons(e, _))", lambda e: infer_exprstmt(e, env)),
        ("key('cond', all(cases, key('case', cons(t, sized(b)))))",
            lambda cases: infer_cond(cases, env)),
        ("key('assert', cons(t, cons(m, _)))",
            lambda t, m: infer_assert(t, m, env)),
        ("key('func', contains(key('args', sized(args))) and \
                      contains(key('body', sized(body))))",
            lambda args, body: infer_func(a, args, body, env)),
        ("key('return', cons(e, _))", lambda e: infer_return(e, env)),
        ("key('returnnothing')", lambda: infer_return(None, env)),
        ("otherwise", lambda e: unknown_infer(e, env)))

def infer_stmts(ss, env):
    substs = {}
    for s in ss:
        substs = compose_substs(infer_stmt(s, env), substs)
    return substs

def infer_types(roots):
    env = Env({}, 1, [])
    substs = infer_stmts(roots, env)
    for a, t in env.envTable.iteritems():
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
