#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from ast import AstType
from globs import TypeOf

TypeCast = new_extrinsic('TypeCast', (Scheme, Scheme))
FieldDT = new_extrinsic('FieldDT', '*DataType')

PROP = new_env('PROP', '*Type')

STMTCTXT = new_env('STMTCTXT', '*Stmt')

PropScope = DT('PropScope', ('retType', 'Maybe(Type)'),
                            ('closedVars', set([TypeVar])))

PROPSCOPE = new_env('PROPSCOPE', 'PropScope')

def with_context(msg):
    return match(env(STMTCTXT),
        ("Just(s)", lambda s: "At:\n%s\n%s" % (s, msg)),
        ("_", lambda: msg))

def global_scope():
    return PropScope(Nothing(), set())

def in_new_scope(retT, f):
    new_scope = PropScope(retT, env(PROPSCOPE).closedVars.copy())
    return in_env(PROPSCOPE, new_scope, f)

def unification_failure(e1, e2, msg):
    assert False, with_context("Couldn't unify %r\nwith %r:\n%s" % (
            e1, e2, msg))

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

def unify_data_and_apply(data, tvars, appTarget, appVar, appArg):
    unify(data, appTarget)
    assert appVar in tvars, "Not a relevant tvar."

def unify(e1, e2):
    same = nop
    fail = lambda m: unification_failure(e1, e2, m)
    match((e1, e2),
        ("(TVar(_), TVar(_))", same), # TEMP
        ("(TTuple(t1), TTuple(t2))",
            lambda t1, t2: unify_tuples(e1, t1, e2, t2, "tuple")),
        ("(TArray(t1), TArray(t2))", unify),
        ("(f1==TFunc(a1, r1), f2==TFunc(a2, r2))", unify_funcs),
        ("(TData(a), TData(b))", lambda a, b: same() if a is b
                                 else fail("mismatched datatypes")),
        ("(e1==TApply(t1,v1,a1), e2==TApply(t2,v2,a2))", unify_applications),
        ("(d==TData(DataType(_, tvs)), TApply(t,v,a))", unify_data_and_apply),
        ("(TApply(t, v, a), d==TData(DataType(_, tvs)))",
            lambda t, v, a, d, tvs: unify_data_and_apply(d, tvs, t, v, a)),
        ("(TInt(), TInt())", same),
        ("(TStr(), TStr())", same),
        ("(TChar(), TChar())", same),
        ("(TBool(), TBool())", same),
        ("(TVoid(), TVoid())", same),
        ("(TTuple(_), TAnyTuple())", same),
        ("(TAnyTuple(), TTuple(_))", same),
        ("(TAnyTuple(), _)", lambda: fail("tuple expected")),
        ("(_, TAnyTuple())", lambda: fail("tuple expected")),
        ("_", lambda: fail("type mismatch")))

def unify_m(e):
    unify(env(PROP), e)

def set_scheme(e, s):
    add_extrinsic(TypeOf, e, s)

def get_type(e, ref):
    return extrinsic(TypeOf, e).type

def pat_tuple(ps):
    ts = match(env(PROP), ("TTuple(ps)", identity))
    assert len(ps) == len(ts), "Tuple pattern length mismatch"
    for p, t in zip(ps, ts):
        in_env(PROP, t, lambda: prop_pat(p))

def pat_var(v):
    set_scheme(v, Scheme([], env(PROP)))

def pat_capture(v, p):
    pat_var(v)
    prop_pat(p)

def pat_ctor(ref, ctor, args):
    ctorT = instantiate_scheme(get_scheme(ctor), ref)
    fieldTs, dt = match(ctorT, ("TFunc(fs, dt)", tuple2))
    unify_m(dt)
    assert len(args) == len(fieldTs), "Wrong ctor param count"
    for arg, fieldT in zip(args, fieldTs):
        in_env(PROP, fieldT, lambda: check_pat(arg))

def prop_pat(p):
    match(p,
        ("PatInt(_)", lambda: unify_m(TInt())),
        ("PatStr(_)", lambda: unify_m(TStr())),
        ("PatWild()", lambda: None),
        ("PatTuple(ps)", pat_tuple),
        ("PatVar(v)", pat_var),
        ("PatCapture(v, p)", pat_capture),
        ("p==PatCtor(c, args)", pat_ctor))

def prop_binding(binding, ref):
    return match(binding,
        ("BindVar(v) or BindCtor(v)", lambda v: get_type(v, ref)),
        ("BindBuiltin(b)",
                lambda b: instantiate_scheme(builtin_scheme(b), ref)),
    )

def prop_call(f, s):
    ft = prop_expr(f)
    argts = map(prop_expr, s)
    assert len(ft.funcArgs) == len(argts), "Arg count mismatch"
    for t1, t2 in zip(ft.funcArgs, argts):
        unify(t1, t2)
    return ft.funcRet

def prop_logic(l, r):
    check_expr(TBool(), l)
    check_expr(TBool(), r)
    return TBool()

def prop_func(e, f, ps, b):
    tvars = {}
    fannot = in_env(TVARS, tvars, lambda: parse_type(extrinsic(AstType, f)))
    tps, tret = match(fannot, ('TFunc(tps, tret)', tuple2))
    set_scheme(f, Scheme(tvars.values(), fannot))
    assert len(tps) == len(ps), "Mismatched param count: %s\n%s" % (tps, ps)
    def inside_func_scope():
        closed = env(PROPSCOPE).closedVars
        for tvar in tvars.itervalues():
            closed.add(tvar)
        for p, tp in zip(ps, tps):
            set_scheme(p, Scheme([], tp))
        prop_body(b)
        return fannot
    return in_new_scope(Just(tret), inside_func_scope)

def prop_match(m, e, cs):
    et = prop_expr(e)
    retT = Nothing()
    for c in cs:
        cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))
        def prop_case():
            in_env(PROP, et, lambda: prop_pat(cp))
            rt = prop_expr(ce)
            retT = env(PROPSCOPE).retType
            if isJust(retT):
                t = m.arg
                unify(rt, fromJust(retT))
            else:
                retT = Just(rt)
            return retT
        retT = in_new_scope(retT, prop_case)
    return fromJust(retT)

def prop_attr(s, f, ft):
    check_expr(TData(extrinsic(FieldDT, f)), s)
    return ft

def prop_getenv(environ):
    return stuff

def prop_inenv(environ, init, f):
    return stuff

def unknown_prop(a):
    assert False, with_context('Unknown prop case:\n%s' % (a,))

def prop_expr(e):
    return match(e,
        ("IntLit(_)", lambda: TInt()),
        ("StrLit(_)", lambda: TStr()),
        ("TupleLit(ts)", lambda ts: TTuple(map(prop_expr, ts))),
        ("ListLit(ss)", lambda ts: TList(map(prop_expr, ts))),
        ("Call(f, s)", prop_call),
        ("And(l, r)", prop_logic),
        ("Or(l, r)", prop_logic),
        ("e==FuncExpr(f==Func(ps, b))", prop_func),
        ("m==Match(p, cs)", prop_match),
        ("Attr(s, f==Field(ft))", prop_attr),
        ("GetCtxt(environ)", prop_getenv),
        ("InCtxt(environ, init, f)", prop_inenv),
        ("Bind(b)", lambda b: prop_binding(b, e)),
        ("_", lambda: unknown_prop(e)))

def check_expr(t, e):
    unify(t, prop_expr(e))

def check_lhs(tv, lhs):
    in_env(PROP, tv, lambda: match(lhs,
        ("LhsAttr(s, f)", lambda s, f: check_attr_lhs(s, f, lhs)),
        ("LhsVar(v)", lambda v: unify_m(get_type(v, tv))),
        ("_", lambda: unknown_prop(lhs))))

def prop_lhs(a):
    tv = fresh()
    check_lhs(tv, a)
    return tv

def prop_DT(form):
    dtT = TData(form)
    for c in form.ctors:
        fieldTs = []
        for f in c.fields:
            add_extrinsic(FieldDT, f, form)
            fieldTs.append(f.type)
        funcT = TFunc(fieldTs, dtT)
        # TODO: Should use only the typevars that appear in this ctor
        cT = Scheme(form.tvars, funcT)
        set_scheme(c, cT)

def prop_new_env(environ):
    # TODO
    pass

def prop_new_extrinsic(ext):
    # XXX: Should have a declarative area for this kind of stuff
    #      so I can unify all this lookup business
    pass

def prop_defn(a, e):
    set_scheme(a, Scheme([], prop_expr(e)))

def prop_assign(a, e):
    t = prop_lhs(a)
    check_expr(t, e)

def prop_augassign(a, e):
    check_lhs(TInt(), a)
    check_expr(TInt(), e)

def prop_cond(cases, else_):
    for t, b in cases:
        check_expr(TBool(), t)
        prop_body(b)
    if isJust(else_):
        prop_body(fromJust(else_))

def prop_while(test, body):
    check_expr(TBool(), test)
    prop_body(body)

def prop_assert(tst, msg):
    check_expr(TBool(), tst)
    check_expr(TStr(), msg)

def prop_return(e):
    check_expr(env(PROPSCOPE).retType.just, e)

def prop_returnnothing():
    assert isNothing(env(PROPSCOPE).retType), "Returned nothing"

def prop_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(var, e)", prop_defn),
        ("Assign(lhs, e)", prop_assign),
        ("AugAssign(_, lhs, e)", prop_augassign),
        ("Break()", nop),
        ("ExprStmt(e)", prop_expr),
        ("Cond(cases, elseCase)", prop_cond),
        ("While(t, b)",prop_while),
        ("Assert(t, m)", prop_assert),
        ("Return(e)", prop_return),
        ("ReturnNothing()", prop_returnnothing),
        ("otherwise", unknown_prop)))

def prop_body(body):
    for s in body.stmts:
        prop_stmt(s)

def prop_top_level(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("TopDT(form)", prop_DT),
        ("TopCtxt(environ)", prop_new_env),
        ("TopDefn(var, e)", prop_defn),
        ("TopExtrinsic(extr)", prop_new_extrinsic),
        ("otherwise", unknown_prop)))

def prop_compilation_unit(unit):
    for s in unit.tops:
        prop_top_level(s)

def with_fields(func):
    def go():
        # Ought to just do this globally.
        """
        for dt in DATATYPES.itervalues():
            prop_DT(dt.__form__)
        """
        return func()
    return scope_extrinsic(FieldDT, go)

def nop():
    pass

def prop_types(root):
    captures = {}
    annots = {}
    in_env(PROPSCOPE, global_scope(),
        lambda: capture_scoped([TypeCast], captures,
        lambda: capture_extrinsic(TypeOf, annots,
        lambda: in_new_scope(Nothing(),
        lambda: with_fields(
        lambda: prop_compilation_unit(root)
    )))))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
