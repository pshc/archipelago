#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from globs import TypeOf

TypeCast = new_extrinsic('TypeCast', (Scheme, Scheme))
FieldDT = new_extrinsic('FieldDT', '*DataType')

ALGM = new_env('ALGM', '*Type')

STMTCTXT = new_env('STMTCTXT', '*Stmt')

HmScope = DT('HmScope', ('table', {'*Expr': (Scheme, bool)}),
                        ('retType', Type),
                        ('returned', 'Maybe(bool)'),
                        ('prev', 'HmScope'))

HMSCOPE = new_env('HMSCOPE', HmScope)

def fresh():
    return TMeta(Nothing())

def with_context(msg):
    return match(env(STMTCTXT),
            ("Just(s)", lambda s: "At:\n%s\n%s" % (s, msg)),
            ("_", lambda: msg))

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

def unify_applications(e1, t1, v1, a1, e2, t2, v2, a2):
    unify(t1, t2)
    if v1 == v2:
        unify(a1, a2)
    else:
        assert False("TODO: Save this info in schemes")

def unify_data_and_apply(data, appTarget, appVar, appArg):
    unify(data, appTarget)
    assert appVar in data.tvars, "Not a relevant tvar."

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
        ("(TArray(t1), TArray(t2))", unify),
        ("(f1==TFunc(a1, r1), f2==TFunc(a2, r2))", unify_funcs),
        ("(TData(a), TData(b))", lambda a, b: same() if a is b
                                 else fail("mismatched datatypes")()),
        ("(e1==TApply(t1,v1,a1), e2==TApply(t2,v2,a2))", unify_applications),
        ("(TData(d), TApply(t, v, a))", unify_data_and_apply),
        ("(TApply(t, v, a), TData(d))",
            lambda t, v, a, d: unify_data_and_apply(d, t, v, a)),
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

def unify_m(e):
    unify(env(ALGM), e)

def set_scheme(e, s, save):
    scope = env(HMSCOPE)
    while scope is not None:
        assert e not in scope.table, "%s already has a type" % (e,)
        scope = scope.prev
    env(HMSCOPE).table[e] = (s, save)

def set_monotype(e, t, save):
    set_scheme(e, Scheme([], t), save)

def get_scheme(e):
    scope = env(HMSCOPE)
    while scope is not None:
        if e in scope.table:
            s, aug = scope.table[e]
            return s
        scope = scope.prev
    assert has_extrinsic(TypeOf, e), with_context('%s not in scope' % (e,))
    return extrinsic(TypeOf, e)

def in_new_scope(f):
    new_scope = HmScope({}, None, False, env(HMSCOPE))
    ret = in_env(HMSCOPE, new_scope, f)

    # Save augmentations from that scope
    for e, info in new_scope.table.iteritems():
        s, save = info
        if save:
            add_extrinsic(TypeOf, e, s)

    return ret

def instantiate_scheme(s, astRef):
    vs, t = match(s, ('Scheme(vs, t)', tuple2))
    if len(vs) > 0:
        repl = dict((v, fresh()) for v in vs)
        t = map_type_vars(lambda v: repl.get(v.typeVar, v), t)
        # Need to supplement AST with any casts if required
        add_extrinsic(TypeCast, astRef, (s, t))
    return t

def generalize_type(t, polyEnv):
    metas = free_meta_vars(t)
    while polyEnv is not None:
        for scope in polyEnv.table:
            metas = metas.difference(free_meta_vars(scope))
        polyEnv = polyEnv.prev
    tvs = []
    for i, meta in enumerate(metas):
        tv = TypeVar()
        add_extrinsic(Name, tv, chr(97 + i))
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

def check_tuple(ts):
    unify_m(TTuple(map(infer_expr, ts)))

def check_list(elems):
    elemT = fresh()
    for elem in elems:
        check_expr(elemT, elem)
    unify_m(TArray(elemT))

def decompose_func_type(ft, nargs):
    argTs, retT = match(ft, ("TFunc(argTs, retT)", tuple2),
                            ("_", lambda: ([], None)))
    if retT is None:
        argTs = [fresh() for n in range(nargs)]
        retT = fresh()
        unify(ft, TFunc(argTs, retT))
    assert len(argTs) == nargs
    return (argTs, retT)

def check_call(f, args):
    argTs, retT = decompose_func_type(infer_expr(f), len(args))
    for argT, arg in zip(argTs, args):
        check_expr(argT, arg)
    unify_m(retT)

def check_logic(l, r):
    check_expr(TBool(), l)
    check_expr(TBool(), r)
    unify_m(TBool())

def check_funcexpr(funcExpr, f, params, b):
    s = infer_func_scheme(f, params, b)
    set_scheme(f, s, True)
    t = instantiate_scheme(s, funcExpr) # stupidest hack
    unify_m(t)

def pat_var(v):
    set_monotype(v, env(ALGM), True)

def pat_capture(v, p):
    pat_var(v)
    check_pat(p)

# XXX: Instantiation has to be consistent across all match cases...
def pat_ctor(ctor, args, ref):
    ctorT = instantiate_scheme(get_scheme(ctor), ref)
    fieldTs, dt = match(ctorT, ("TFunc(fs, dt)", tuple2))
    unify_m(dt)
    assert len(args) == len(fieldTs), "Wrong ctor param count"
    for arg, fieldT in zip(args, fieldTs):
        check_pat(fieldT, arg)

def check_pat(p):
    match(p,
        ("PatInt(_)", lambda: unify_m(TInt())),
        ("PatStr(_)", lambda: unify_m(TStr())),
        ("PatWild()", lambda: None),
        ("PatTuple(ps)", lambda ps: unify_m(TTuple(map(infer_pat, ps)))),
        ("PatVar(v)", pat_var),
        ("PatCapture(v, p)", pat_capture),
        ("PatCtor(c, args)", lambda c, args: pat_ctor(c, args, p))
        )

def infer_pat(p):
    tv = fresh()
    in_env(ALGM, tv, lambda: check_pat(p))
    return tv

def check_match(m, e, cs):
    retT = env(ALGM)
    et = infer_expr(e)
    for c in cs:
        cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))
        def check_case():
            in_env(ALGM, et, lambda: check_pat(cp))
            check_expr(retT, ce)
        in_new_scope(check_case)
    # Help out C transmogrification with some extra type annotations
    set_monotype(m, retT, True)
    set_monotype(e, et, True)

def check_attr(struct, f, ref):
    # Would be nice if we didn't have to instantiate a TData pointlessly
    # every time, but then we'd have to start garbage collecting a shared one
    check_expr(TData(extrinsic(FieldDT, f)), struct)
    unify_m(get_type(f, ref))

def check_attr_lhs(struct, f, ref):
    check_lhs(TData(extrinsic(FieldDT, f)), struct)
    unify_m(get_type(f, ref))

def check_getenv(environ):
    global ENV
    # TODO: Add env to func scope
    unify_m(ENV.omniEnv.omniContextTypes[environ])

def check_inenv(environ, init, f):
    global ENV
    t = ENV.omniEnv.omniContextTypes[environ]
    check_expr(t, init)
    # TODO: Add env to func attributes
    check_expr(TFunc([], env(ALGM)), f)

def unknown_infer(a):
    assert False, with_context('Unknown infer case:\n%s' % (a,))

def builtin_scheme(builtin):
    return builtin_type(extrinsic(Name, builtin))

def check_binding(binding, ref):
    unify_m(match(binding,
        ("BindVar(v)", lambda v: get_type(v, ref)),
        ("BindBuiltin(b)",
                lambda b: instantiate_scheme(builtin_scheme(b), ref)),
    ))

def check_builtin(s, ref):
    unify_m(instantiate_scheme(atoms_to_scheme(s), ref))

def check_expr(tv, e):
    """Algorithm M."""
    in_env(ALGM, tv, lambda: match(e,
        ("IntLit(_)", lambda: unify(tv, TInt())),
        ("StrLit(_)", lambda: unify(tv, TStr())),
        ("TupleLit(ts)", check_tuple),
        ("ListLit(ss)", check_list),
        ("Call(f, s)", check_call),
        ("And(l, r)", check_logic),
        ("Or(l, r)", check_logic),
        ("e==FuncExpr(f==Func(ps, b))", check_funcexpr),
        ("m==Match(p, cs)", check_match),
        ("Attr(s, f)", lambda s, f: check_attr(s, f, e)),
        ("GetCtxt(environ)", check_getenv),
        ("InCtxt(environ, init, f)", check_inenv),
        ("Bind(b)", lambda b: check_binding(b, e)),
        ("_", lambda: unknown_infer(e))))

def infer_expr(e):
    tv = fresh()
    check_expr(tv, e)
    return tv

def check_lhs(tv, lhs):
    in_env(ALGM, tv, lambda: match(lhs,
        ("LhsAttr(s, f)", lambda s, f: check_attr_lhs(s, f, lhs)),
        ("LhsVar(v)", lambda v: unify_m(get_type(v, tv))),
        ("_", lambda: unknown_infer(lhs))))

def infer_lhs(a):
    tv = fresh()
    check_lhs(tv, a)
    return tv

def infer_DT(form):
    dtT = TData(form)
    for c in form.ctors:
        fieldTs = []
        for f in c.fields:
            add_extrinsic(FieldDT, f, form)
            fieldTs.append(f.type)
        funcT = TFunc(fieldTs, dtT)
        # TODO: Should use only the typevars that appear in this ctor
        cT = Scheme(form.tvars, funcT)
        set_scheme(c, cT, True)

def infer_new_env(environ):
    # TODO
    pass

def infer_new_extrinsic(ext):
    # XXX: Should have a declarative area for this kind of stuff
    #      so I can unify all this lookup business
    pass

def infer_defn(a, e):
    t = fresh()
    check_expr(t, e)
    set_scheme(a, generalize_type(t, env(HMSCOPE)), True)

def infer_assign(a, e):
    t = infer_lhs(a)
    check_expr(t, e)

def infer_augassign(a, e):
    check_lhs(TInt(), a)
    check_expr(TInt(), e)

def infer_cond(cases, else_):
    for t, b in cases:
        check_expr(TBool(), t)
        infer_body(b)
    if isJust(else_):
        infer_body(fromJust(else_))

def infer_while(test, body):
    check_expr(TBool(), test)
    infer_body(body)

def infer_assert(tst, msg):
    check_expr(TBool(), tst)
    check_expr(TStr(), msg)

def infer_func_scheme(f, params, body):
    def inside_func_scope():

        retT = fresh()
        env(HMSCOPE).retType = retT
        funcT = fresh()
        if f is not None:
            set_monotype(f, funcT, False)
        paramTs = []
        for p in params:
            t = fresh()
            set_monotype(p, t, False)
            paramTs.append(t)

        infer_body(body)

        scope = env(HMSCOPE)
        if not matches(scope.returned, "Just(True)"):
            unify(retT, TVoid())
        unify(funcT, TFunc(paramTs, retT))
        return generalize_type(funcT, scope)
    return in_new_scope(inside_func_scope)

def infer_return(e):
    scope = env(HMSCOPE)
    assert not matches(scope.returned, 'Just(False)'), "Returned nothing"
    check_expr(env(HMSCOPE).retType, e)
    scope.returned = Just(True)

def infer_returnnothing():
    scope = env(HMSCOPE)
    assert not matches(scope.returned, 'Just(True)'), "Returned something"
    scope.returned = Just(False)

def infer_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(var, e)", infer_defn),
        ("Assign(lhs, e)", infer_assign),
        ("AugAssign(_, lhs, e)", infer_augassign),
        ("Break()", nop),
        ("ExprStmt(e)", infer_expr),
        ("Cond(cases, elseCase)", infer_cond),
        ("While(t, b)",infer_while),
        ("Assert(t, m)", infer_assert),
        ("Return(e)", infer_return),
        ("ReturnNothing()", infer_returnnothing),
        ("otherwise", unknown_infer)))

def infer_body(body):
    for s in body.stmts:
        infer_stmt(s)

def infer_top_level(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("TopDT(form)", infer_DT),
        ("TopCtxt(environ)", infer_new_env),
        ("TopDefn(var, e)", infer_defn),
        ("TopExtrinsic(extr)", infer_new_extrinsic),
        ("otherwise", unknown_infer)))

def infer_compilation_unit(unit):
    for s in unit.tops:
        infer_top_level(s)

def with_fields(func):
    def go():
        # Ought to just do this globally.
        """
        for dt in DATATYPES.itervalues():
            infer_DT(dt.__form__)
        """
        return func()
    return scope_extrinsic(FieldDT, go)

def nop():
    pass

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
                        TFunc(map(normalize_type, args),
                              normalize_type(ret))),
                    ("TTuple(ts)", lambda ts: TTuple(map(normalize_type, ts))),
                    ("TApply(t, v, a)", lambda t, v, a:
                        TApply(normalize_type(t), v, normalize_type(a))),
                    ("_", lambda: t))

def normalize_scheme(s):
    s.type = normalize_type(s.type)
    return s

def infer_types(root):
    captures = {}
    annots = {}
    in_env(HMSCOPE, None,
        lambda: capture_scoped([TypeCast], captures,
        lambda: capture_extrinsic(TypeOf, annots,
        lambda: in_new_scope(
        lambda: with_fields(
        lambda: infer_compilation_unit(root)
    )))))

    casts = {}
    for e, (s, t) in captures[TypeCast].iteritems():
        if not type_equal(s.type, t):
            casts[e] = normalize_type(t)
    for e in annots.keys():
        norm = normalize_scheme(annots[e])
        annots[e] = norm
        update_extrinsic(TypeOf, e, norm)
    captures[TypeOf] = annots
    return captures

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
