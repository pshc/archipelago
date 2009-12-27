#!/usr/bin/env python
from atom import *
from base import *
from builtins import *
from types_builtin import *

OmniEnv = DT('OmniEnv', ('omniTable', {Atom: Scheme}),
                        ('omniInsts', {Atom: [Type]}),
                        ('omniFieldDTs', {Atom: Atom}),
                        ('omniIndex', int))

Env = DT('Env', ('envTable', {Atom: Scheme}),
                ('envRetType', Type),
                ('envReturned', bool),
                ('envPrev', 'Env'))

GlobalEnv = DT('GlobalEnv', ('omniEnv', OmniEnv),
                            ('curEnv', Env))

ENV = None

def fresh():
    global ENV
    i = ENV.omniEnv.omniIndex
    ENV.omniEnv.omniIndex = i + 1
    return TVar(symref('typevar', [symname('a%d' % (i,))]))

def fresh_from(v):
    nm = getname(v)
    return TVar(symref('typevar', [symname("%s'" % (nm,))]))

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

def free_vars_in_env(env):
    if env is None:
        return set()
    fvs = free_vars_in_env(env.envPrev)
    for k, s in env.envTable.iteritems():
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
    if match(e, ("TVar(n2)", lambda n2: n is n2), ("_", lambda: False)):
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
        ("(TData(a), TData(b))", lambda a, b: {} if a is b else fail()),
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

def set_type(e, t, substs, augment_ast):
    global ENV
    gt = generalize_type(apply_substs(substs, t))
    ENV.curEnv.envTable[e] = gt
    if augment_ast:
        ENV.omniEnv.omniTable[e] = gt

def get_type(e):
    global ENV
    env = ENV.curEnv
    while e not in env.envTable:
        env = env.envPrev
        assert env is not None, '%s not found in env' % (e,)
    return env.envTable[e]

def in_new_env(f, data):
    global ENV
    outerEnv = ENV.curEnv
    ENV.curEnv = Env({}, None, False, outerEnv)

    ret = f(ENV.curEnv, data)

    ENV.curEnv = outerEnv
    return ret

def generalize_type(t):
    global ENV
    evs = free_vars_in_env(ENV.curEnv)
    gen_vars = free_vars(t).difference(evs)
    return Scheme(gen_vars, t)

def instantiate_with_type(ref, scheme):
    global ENV
    vs, t = match(scheme, ("Scheme(vs, t)", tuple2))
    insts = [(v, fresh_from(v)) for v in vs]
    if len(insts) > 0:
        assert ref not in insts
        ENV.omniEnv.omniInsts[ref] = insts
    return apply_substs(dict(insts), t)

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

def pat_tuple(ps):
    s = {}
    tupTs = []
    for p in ps:
        pT, s2 = infer_pat(p)
        s = compose(s, s2)
        list_append(tupTs, pT)
    return (TTuple(tupTs), s)

def pat_var(v):
    t = fresh()
    set_type(v, t, {}, True)
    return (t, {})

def pat_capture(v, p):
    pat_var(v)
    return infer_pat(p)

def pat_ctor(ctor, args):
    ct = get_type(ctor).schemeType
    fieldTs, dt = match(ct, ("TFunc(fs, dt)", tuple2))
    s = {}
    for a, ft in zip(args, fieldTs):
        argT, s2 = infer_pat(a)
        s = compose(unify(argT, ft), compose(s, s2))
    return (dt, s)

def infer_pat(p):
    return match(p,
        ("Int(_, _)", lambda: (TInt(), {})),
        ("Str(_, _)", lambda: (TStr(), {})),
        ("key('wildcard')", lambda: (fresh(), {})),
        ("key('tuplelit', sized(ps))", pat_tuple),
        ("v==key('var')", pat_var),
        ("key('capture', cons(v, cons(p, _)))", pat_capture),
        ("key('ctor', cons(Ref(c, _, _), sized(args)))", pat_ctor),
        )

def infer_match(m, e, cs):
    et, s = infer_expr(e)
    retT = fresh()
    for c in cs:
        cp, ce = match(c, ("key('case', cons(p, cons(e, _)))", tuple2))
        def infer_case(env, s):
            pt, s2 = infer_pat(cp)
            s = compose(unify(et, pt), compose(s, s2))
            t, s2 = infer_expr(ce)
            return compose(unify(t, retT), compose(s, s2))
        s = in_new_env(infer_case, s)
    # Help out C transmogrification with some extra type annotations
    set_type(m, retT, s, True)
    set_type(e, et, s, True)
    return (retT, s)

def infer_attr(struct, a):
    global ENV
    structT, s = infer_expr(struct)
    adt = ENV.omniEnv.omniFieldDTs[a]
    s = compose(unify(TData(adt), structT), s)
    return (get_type(a).schemeType, s)

def unknown_infer(a):
    assert False, 'Unknown infer case:\n%s' % (a,)

def infer_expr(a):
    return match(a,
        ("Int(_, _)", lambda: (TInt(), {})),
        ("Str(_, _)", lambda: (TStr(), {})),
        ("key('char')", lambda: (TChar(), {})),
        ("key('tuplelit', sized(ts))", infer_tuple),
        ("key('call', cons(f, sized(s)))", infer_call),
        ("m==key('match', cons(e, all(cs, c==key('case'))))", infer_match),
        ("key('attr', cons(s, cons(Ref(a, _, _), _)))", infer_attr),
        ("Ref(v==key('var'), _, _)",
            lambda v: (get_type(v).schemeType, {})),
        ("Ref(f==key('func' or 'ctor'), _, _)",
            lambda f: (instantiate_with_type(a, get_type(f)), {})),
        ("Ref(key('symbol', contains(t==key('type'))), _, _)",
            lambda t: (instantiate_with_type(a, atoms_to_scheme(t)), {})),
        ("otherwise", unknown_infer))

def infer_DT(dt, cs, vs, nm):
    dtT = TData(dt)
    for c in cs:
        fieldTs = []
        for f in match(c, ("key('ctor', all(fs, f==key('field')))", identity)):
            t = match(f, ("key('field', contains(key('type', cons(t, _))))",
                          lambda t: atoms_to_type(t)))
            list_append(fieldTs, t)
            set_type(f, t, {}, False)
        set_type(c, TFunc(fieldTs, dtT), {}, False)
    return {}

def infer_assign(a, e):
    newvar = match(a, ("key('var')", lambda: True),
                      ("Ref(key('var'), _, _)", lambda: False))
    t = fresh() if newvar else get_type(a.refAtom).schemeType
    et, substs = infer_expr(e)
    substs = compose(substs, unify(t, et))
    if newvar:
        set_type(a, t, substs, True)
    return substs

def infer_exprstmt(e):
    t, substs = infer_expr(e)
    return substs

def infer_cond(subs, cases):
    s = {}
    for t, b in cases:
        tt, ts = infer_expr(t)
        s = compose(ts, s)
        s = compose(unify(tt, TBool()), s)
        s = compose(infer_stmts(b), s)
    else_ = match(subs, ('contains(key("else", sized(body)))', identity),
                        ('_', lambda: None))
    if else_ is not None:
        s = compose(infer_stmts(else_), s)
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

def _inside_func_env(env, info):
    retT = fresh()
    env.envRetType = retT
    f, args, body = info
    funcT = fresh()
    set_type(f, funcT, {}, False)
    argTs = [fresh() for arg in args]
    for a, t in zip(args, argTs):
        set_type(a, t, {}, False)

    s = infer_stmts(body)

    if not env.envReturned:
        retT = TVoid()
    s = compose(unify(funcT, TFunc(argTs, retT)), s)
    return (s, funcT, argTs)

def infer_func(f, args, body):
    s, funcT, argTs = in_new_env(_inside_func_env, (f, args, body))
    set_type(f, funcT, s, True)
    for a, t in zip(args, argTs):
        set_type(a, t, s, True)
    return s

def infer_return(e):
    global ENV
    if e is not None:
        t, s = infer_expr(e)
        ENV.curEnv.envReturned = True
        return compose(unify(ENV.curEnv.envRetType, t), s)
    return {}

def infer_stmt(a):
    return match(a,
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
    substs = {}
    for s in ss:
        substs = compose(infer_stmt(s), substs)
    return substs

def setup_infer_env(roots):
    fields = {}
    for dt in roots:
        cs = match(dt, ("key('DT', all(cs, c==key('ctor')))", identity),
                       ("_", lambda: []))
        for c in cs:
            fs = match(c, ("key('ctor', all(fs, f==key('field')))", identity))
            for f in fs:
                fields[f] = dt
    omni = OmniEnv({}, {}, fields, 1)
    env = Env({}, None, False, None)
    return GlobalEnv(omni, env)

def infer_types(roots):
    global ENV
    ENV = setup_infer_env(roots)
    substs = infer_stmts(roots)
    for a, t in ENV.omniEnv.omniTable.iteritems():
        apply_substs_to_scheme(substs, t)
        a.subs.append(scheme_to_atoms(t))
    for r, ts in ENV.omniEnv.omniInsts.iteritems():
        for t, tv in ts:
            it = type_to_atoms(apply_substs(substs, tv))
            r.subs.append(symref('instantiation', [Ref(t, None, []), it]))

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short)
    infer_types(short.roots)
    write_mod_repr('hello', short)
    serialize_module(short)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
