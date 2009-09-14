#!/usr/bin/env python
from atom import *
from base import *
from builtins import *
from types_builtin import *

Env = DT('Env', ('envTable', {Atom: Scheme}), # maps AST nodes to type schemes
                ('envIndex', int))

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
    for v in vs:
        if v in s:
            del s[v]
    scheme.schemeType = apply_substs(s, t)

def apply_substs_to_env(substs, env):
    """Modifies in place."""
    ks = dict_keys(env)
    for k in ks:
        env[k] = apply_substs(substs, env[k])

def apply_substs(substs, t):
    return map_type_vars(lambda t, s: s.get(t, t), t, substs)

def compose_substs(s1, s2):
    s3 = s1.copy()
    for k, v in s2.iteritems():
        s3[k] = apply_substs(s1, v)
    return s3

def free_vars_in_substs(substs):
    fvs = set()
    for k, s in substs.iteritems():
        fvs.update(free_vars(s))
    return fvs

def free_vars_in_func(args, ret):
    # Don't bother with reduce and union for ease of C conversion
    fvs = set()
    for a in args:
        fvs.update(free_vars(a))
    fvs.update(free_vars(ret))
    return fvs

def free_vars(v):
    return match(v, ("TVar(_)", lambda: set([v])),
                    ("TFunc(args, ret)", free_vars_in_func),
                    ("_", lambda: set()))

def unify_funcs(f1, args1, ret1, f2, args2, ret2, env):
    if len(args1) != len(args2):
        unification_failure(f1, f2, env)
    s = {}
    for a1, a2 in zip(args1, args2):
        a1 = apply_substs(s, a1)
        a2 = apply_substs(s, a2)
        s = compose_substs(s, unify(a1, a2, env))
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
    return match((e1, e2),
        ("(TVar(_), _)", lambda: unify_bind(e1, e2, env)),
        ("(_, TVar(_))", lambda: unify_bind(e2, e1, env)),
        ("(TFunc(a1, r1), TFunc(a2, r2))", lambda a1, r1, a2, r2:
            unify_funcs(e1, a1, r1, e2, a2, r2, env)),
        # These two must be last
        ("(TInt(), TInt())", lambda: {}),
        ("(TStr(), TStr())", lambda: {}),
        ("(TBool(), TBool())", lambda: {}),
        ("(TVoid(), TVoid())", lambda: {}),
        ("_", lambda: unification_failure(e1, e2, env)))

def set_type(e, t, env, substs):
    env.envTable[e] = generalize_type(apply_substs(substs, t), substs)

def get_type(e, env):
    return instantiate_type(env.envTable[e], env)

def generalize_type(t, substs):
    gen_vars = free_vars(t).difference(free_vars_in_substs(substs))
    return Scheme(gen_vars, t)

def instantiate_type(scheme, env):
    vs, t = match(scheme, ("Scheme(vs, t)", tuple2))
    vs_substs = [(v, fresh(env)) for v in vs]
    return apply_substs(dict(vs_substs), t)

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
    assert False, 'Unknown type for:\n%s' % (a,)

def infer_expr(a, env):
    return match(a,
        ("Int(_, _)", lambda: (TInt(), {})),
        ("Str(_, _)", lambda: (TStr(), {})),
        ("key('call', cons(f, sized(s)))", lambda f, s: infer_call(f, s, env)),
        ("Ref(v==key('var'), _, _)", lambda v: (get_type(v, env), {})),
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
        ("otherwise", lambda e: unknown_infer(e, env)))

def infer_stmts(ss, env):
    substs = {}
    for s in ss:
        substs = compose_substs(infer_stmt(s, env), substs)
    return substs

def infer_types(roots):
    env = Env({}, 1)
    substs = infer_stmts(roots, env)
    for a, t in env.envTable.iteritems():
        apply_substs_to_scheme(substs, t)
        a.subs.append(scheme_to_atoms(t))

def write_mod_repr(filename, m):
    f = fopen(filename, 'w')
    for r in m.roots:
        fwrite(f, repr(r))
    fclose(f)

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short)
    infer_types(short.roots)
    write_mod_repr('hello', short)
    serialize_module(short)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
