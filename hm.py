#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
import globs

OmniEnv = DT('OmniEnv', ('omniTypeAnnotations', {Atom: Scheme}),
                        ('omniTypeCasts', {Atom: (Scheme, Scheme)}),
                        ('omniFieldDTs', {Atom: Atom}),
                        ('omniContextTypes', {Atom: Atom}),
                        ('omniASTContext', 'Maybe(Atom)'))

Env = DT('Env', ('envTable', {Atom: Scheme}),
                ('envRetType', Type),
                ('envReturned', bool),
                ('envPrev', 'Env'))

GlobalEnv = DT('GlobalEnv', ('omniEnv', OmniEnv),
                            ('curEnv', Env))

ENV = None
LIST_TYPE = None

loaded_export_atom_types = {}

def fresh():
    return TMeta(Nothing())

def with_context(msg):
    global ENV
    if isJust(ENV.omniEnv.omniASTContext):
        return "At:\n%s\n%s" % (ENV.omniEnv.omniASTContext.just, msg)
    return msg

def unification_failure(e1, e2, msg):
    assert False, with_context("Couldn't unify %r with %r: %s" % (e1, e2, msg))

def unify_tuples(t1, list1, t2, list2, desc):
    if len(list1) != len(list2):
        unification_failure(t1, t2, "%s length mismatch" % (desc,))
    for a1, a2 in zip(list1, list2):
        unify(a1, a2)

def unify_funcs(f1, args1, ret1, f2, args2, ret2):
    unify_tuples(f1, args1, f2, args2, "func params")
    unify(ret1, ret2)

def unify_applications(e1, t1, ss1, e2, t2, ss2):
    unify(t1, t2)
    unify_tuples(e1, ss1, e2, ss2, "type arguments")

def unify_data_and_apply(data, appType, appArgs):
    unify(data, appType)
    # TODO: OH GOD

def unify_metas(t1, t2):
    if isNothing(t1.metaType):
        if isNothing(t2.metaType):
            t1.metaType = Just(t2)
        else:
            t1.metaType = t2.metaType
    elif isNothing(t2.metaType):
        t2.metaType = t1.metaType
    else:
        unify(fromJust(t1.metaType), fromJust(t2.metaType))

def unify_bind_meta(meta, t):
    if isNothing(meta.metaType):
        meta.metaType = Just(t)
    else:
        unify(fromJust(meta.metaType), t)

def unify(e1, e2):
    global ENV
    same = lambda: None
    fail = lambda m: lambda: unification_failure(e1, e2, m)
    match((e1, e2),
        ("(m1==TMeta(_), m2==TMeta(_))", unify_metas),
        ("(TMeta(_), _)", lambda: unify_bind_meta(e1, e2)),
        ("(_, TMeta(_))", lambda: unify_bind_meta(e2, e1)),
        ("(TVar(v1), TVar(v2))", lambda v1, v2: same() if v1 is v2
                                 else fail("mismatched type vars")),
        ("(TTuple(t1), TTuple(t2))",
            lambda t1, t2: unify_tuples(e1, t1, e2, t2, "tuple")),
        ("(e1==TFunc(a1, r1), e2==TFunc(a2, r2))", unify_funcs),
        ("(TData(a), TData(b))", lambda a, b: same() if a is b
                                 else fail("mismatched datatypes")()),
        ("(e1==TApply(t1, ss1), e2==TApply(t2, ss2))", unify_applications),
        ("(a==TData(_), TApply(b, bs))", unify_data_and_apply),
        ("(TApply(b, bs), a==TData(_))",
            lambda b, bs, a: unify_data_and_apply(a, b, bs)),
        ("(TInt(), TInt())", same),
        ("(TStr(), TStr())", same),
        ("(TChar(), TChar())", same),
        ("(TBool(), TBool())", same),
        ("(TVoid(), TVoid())", same),
        ("(TTuple(_), TAnyTuple())", same),
        ("(TAnyTuple(), TTuple(_))", same),
        ("(TAnyTuple(), _)", fail("tuple expected")),
        ("(_, TAnyTuple())", fail("tuple expected")),
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
    # XXX: For now, try to import from EVERY LOADED MODULE?!
    t = loaded_export_atom_types.get(e)
    assert t is not None, with_context('%s not in scope' % (e,))
    return t

def in_new_env(f):
    global ENV
    outerEnv = ENV.curEnv
    ENV.curEnv = Env({}, None, False, outerEnv)

    ret = f()

    # Save augmentations from that env
    for e, info in ENV.curEnv.envTable.iteritems():
        s, aug = info
        if aug:
            ENV.omniEnv.omniTypeAnnotations[e] = s

    ENV.curEnv = outerEnv
    return ret

def instantiate_scheme(s, astRef):
    vs, t = match(s, ('Scheme(vs, t)', tuple2))
    if len(vs) > 0:
        repl = dict((v, fresh()) for v in vs)
        t = map_type_vars(lambda v: repl.get(v.varAtom, v), t)
        # Need to supplement AST with any casts if required
        global ENV
        ENV.omniEnv.omniTypeCasts[astRef] = (s, t)
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
        meta.metaType = Just(TVar(tv))
        tvs.append(tv)
    return Scheme(tvs, t)

def get_type(binding, ref):
    return instantiate_scheme(get_scheme(binding), ref)

def free_tuple_meta_vars(ts):
    return reduce(lambda s, t: s.union(_free_metas(t)), ts, set())

def free_func_meta_vars(args, ret):
    return free_tuple_meta_vars(args).union(_free_metas(ret))

def free_apply_meta_vars(t, ss):
    return _free_metas(t).union(free_tuple_meta_vars(ss))

def _free_meta_check(v, j):
    assert isNothing(j), "Normalization failure"
    return set([v])

def _free_metas(t):
    return match(t, ('v==TMeta(j)', _free_meta_check),
                    ('TTuple(ts)', free_tuple_meta_vars),
                    ('TFunc(args, ret)', free_func_meta_vars),
                    ('TApply(t, ss)', free_apply_meta_vars),
                    ('_', lambda: set()))

def free_meta_vars(t):
    return _free_metas(zonk_type(t))

def check_tuple(et, ts):
    unify(et, TTuple(map(infer_expr, ts)))

def check_list(t, elems):
    elemT = fresh()
    for elem in elems:
        check_expr(elemT, elem)
    global LIST_TYPE
    unify(t, TApply(LIST_TYPE, [elemT]))

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

def check_logic(t, l, r):
    check_expr(TBool(), l)
    check_expr(TBool(), r)
    unify(TBool(), t)

def check_lambda(tv, lam, args, b, ref):
    body = [symref('return', [b])] # stupid hack
    s = infer_func_scheme(None, args, body) # non-recursive, so None
    set_scheme(lam, s, True)
    t = instantiate_scheme(s, ref) # stupider hack
    unify(tv, t)

def pat_var(tv, v):
    set_monotype(v, tv, True)

def pat_capture(tv, v, p):
    pat_var(tv, v)
    check_pat(tv, p)

# XXX: Instantiation has to be consistent across all match cases...
def pat_ctor(tv, ctor, args, ref):
    ctorT = instantiate_scheme(get_scheme(ctor), ref)
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
        ("key('ctor', cons(Ref(c, _), sized(args)))",
            lambda c, args: pat_ctor(tv, c, args, p)),
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

def check_attr(tv, struct, a, ref):
    global ENV
    unify(ENV.omniEnv.omniFieldDTs[a], infer_expr(struct))
    unify(tv, get_type(a, ref))

def check_getctxt(tv, ctxt):
    global ENV
    # TODO: Add ctxt to func scope
    unify(tv, ENV.omniEnv.omniContextTypes[ctxt])

def check_inctxt(tv, ctxt, init, f):
    global ENV
    t = ENV.omniEnv.omniContextTypes[ctxt]
    check_expr(t, init)
    # TODO: Add ctxt to func attributes
    check_expr(TFunc([], tv), f)

def unknown_infer(a):
    assert False, with_context('Unknown infer case:\n%s' % (a,))

def check_binding(tv, target, ref):
    unify(tv, get_type(target, ref))

def check_builtin(tv, s, ref):
    unify(tv, instantiate_scheme(atoms_to_scheme(s), ref))

def check_expr(tv, e):
    """Algorithm M."""
    match(e,
        ("Int(_, _)", lambda: unify(tv, TInt())),
        ("Str(_, _)", lambda: unify(tv, TStr())),
        ("key('char')", lambda: unify(tv, TChar())),
        ("key('tuplelit', sized(ts))", lambda ts: check_tuple(tv, ts)),
        ("key('listlit', sized(ss))", lambda ss: check_list(tv, ss)),
        ("key('call', cons(f, sized(s)))", lambda f, s: check_call(tv, f, s)),
        ("key('and' or 'or', cons(l, cons(r, _)))",
            lambda l, r: check_logic(tv, l, r)),
        ("l==key('lambda', sized(args, cons(e, _)))",
            lambda l, a, b: check_lambda(tv, l, a, b, e)),
        ("m==key('match', cons(p, all(cs, c==key('case'))))",
            lambda m, p, cs: check_match(tv, m, p, cs)),
        ("key('attr', cons(s, cons(Ref(a, _), _)))",
            lambda s, a: check_attr(tv, s, a, e)),
        ("key('getctxt', cons(Ref(ctxt, _), _))",
            lambda ctxt: check_getctxt(tv, ctxt)),
        ("key('inctxt', cons(Ref(ctxt, _), cons(init, cons(f, _))))",
            lambda ctxt, init, f: check_inctxt(tv, ctxt, init, f)),
        ("Ref(v==key('var'), _)",
            lambda v: check_binding(tv, v, e)),
        ("Ref(f==key('func' or 'ctor'), _)",
            lambda f: check_binding(tv, f, e)),
        ("Ref(key('symbol', contains(s==key('type'))), _)",
            lambda s: check_builtin(tv, s, e)),
        ("_", lambda: unknown_infer(e)))

def infer_expr(e):
    tv = fresh()
    check_expr(tv, e)
    return tv

def infer_DT(dt, cs, vs, nm):
    dtT = TData(dt)
    tvs = match(dt, ("key('DT', all(tvs, tv==key('typevar')))", identity))
    # TODO: TApply this?
    export_type(dt, TData(dt))
    for c in cs:
        fieldTs = []
        for f in match(c, ("key('ctor', all(fs, f==key('field')))", identity)):
            t = match(f, ("key('field', contains(key('type', cons(t, _))))",
                          lambda t: atoms_to_type(t)))
            fieldTs.append(t)
            set_monotype(f, t, False)
        funcT = TFunc(fieldTs, dtT)
        # TODO: Should use only the typevars that appear in this ctor
        cT = Scheme(tvs, funcT)
        set_scheme(c, cT, True)
        export_type(c, cT)
    if nm == 'List':
        global LIST_TYPE
        LIST_TYPE = dtT

def infer_CTXT(ctxt, t):
    global ENV
    ENV.omniEnv.omniContextTypes[ctxt] = atoms_to_scheme(t).schemeType

def infer_defn(a, e):
    t = fresh()
    check_expr(t, e)
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
            argTs.append(t)

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
    global ENV
    ENV.omniEnv.omniASTContext = Just(a)
    match(a,
        ("dt==key('DT', all(cs, c==key('ctor'))\
                    and all(vs, v==key('typevar'))) and named(nm)", infer_DT),
        ("ctxt==key('CTXT', contains(t==key('type')))", infer_CTXT),
        ("key('defn', cons(a, cons(e, _)))", infer_defn),
        ("key('=', cons(a, cons(e, _)))",
            lambda a, e: check_expr(get_type(a.refAtom, e), e)),
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
    omni = OmniEnv({}, {}, fields, {}, Nothing())
    return GlobalEnv(omni, None)

# Collapse strings of metavars
def _zonk_meta(meta):
    t = meta.metaType
    if isNothing(t):
        return meta
    t = zonk_type(fromJust(t))
    meta.metaType = Just(t)
    return t

def zonk_type(t):
    return match(t, ("m==TMeta(_)", _zonk_meta),
                    ("TFunc(args, ret)", lambda args, ret:
                        TFunc(map(zonk_type, args), zonk_type(ret))),
                    ("TTuple(ts)", lambda ts: TTuple(map(zonk_type, ts))),
                    ("TApply(t, ss)", lambda t, ss:
                        TApply(zonk_type(t), map(zonk_type, ss))),
                    ("_", lambda: t))

# Kill metavars
def normalize_meta(t):
    #assert isJust(t), "Monotype could not be determined"
    return maybe(TVoid(), normalize_type, t)

def normalize_type(t):
    return match(t, ("TMeta(t)", normalize_meta),
                    ("TFunc(args, ret)", lambda args, ret:
                        TFunc(map(normalize_type, args), normalize_type(ret))),
                    ("TTuple(ts)", lambda ts: TTuple(map(normalize_type, ts))),
                    ("TApply(t, ss)", lambda t, ss:
                        TApply(normalize_type(t), map(normalize_type, ss))),
                    ("_", lambda: t))

def normalize_scheme(s):
    s.schemeType = normalize_type(s.schemeType)
    return s

def export_type(atom, t):
    loaded_export_atom_types[atom] = t

def infer_types(roots):
    global ENV
    ENV = setup_infer_env(roots)
    in_new_env(lambda: infer_stmts(roots))
    casts = {}
    for a, (s, t) in ENV.omniEnv.omniTypeCasts.iteritems():
        if not type_equal(s.schemeType, t):
            casts[a] = t
    annots = dict((e, normalize_scheme(s))
                  for e, s in ENV.omniEnv.omniTypeAnnotations.iteritems())
    for root in roots:
        dt = match(root, ("key('DT', _)", lambda: True),
                         ("_", lambda: False))
        if not dt:
            root = match(root, ("key('=', cons(v, _))", identity),
                               ("key('func', _)", lambda: root),
                               ("_", lambda: None))
            if root is not None:
                export_type(root, annots[root])
    return {globs.TypeAnnot: annots, globs.CastAnnot: casts}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
