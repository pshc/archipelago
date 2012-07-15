#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from globs import TypeOf

CHECKSCOPE = new_env('CHECKSCOPE', Type)

CHECK = new_env('CHECK', Type)

def unification_failure(src, dest, msg):
    desc = fmtcol("^DG^Couldn't unify^N {0} {1!r}\n^DG^with^N {2} {3!r}",
            type(src), src, type(dest), dest)
    assert False, with_context(desc, msg)

def try_unite_tuples(src, list1, dest, list2):
    for s, d in ezip(list1, list2):
        try_unite(s, d)

def try_unite_funcs(sf, sargs, sret, df, dargs, dret):
    try_unite_tuples(sf, sargs, df, dargs)
    try_unite(sret, dret)

def try_unite_datas(src, a, ats, dest, b, bts):
    if a is not b:
        unification_failure(src, dest, "mismatched datatypes")
    assert len(ats) == len(a.tvars), "Wrong %s typevar count" % (a,)
    for at, bt in ezip(ats, bts):
        try_unite(at, bt)

def try_unite_prims(src, sp, dest, dp):
    if not prim_equal(sp, dp):
        unification_failure(src, dest, "primitive types")

def try_unite_typevars(src, stv, dest, dtv):
    if stv is not dtv:
        unification_failure(src, dest, "typevars")

def try_unite(src, dest):
    fail = lambda m: unification_failure(src, dest, m)
    match((src, dest),
        ("(src==TVar(stv), dest==TVar(dtv))", try_unite_typevars),
        ("(src==TTuple(t1), dest==TTuple(t2))", try_unite_tuples),
        ("(TArray(t1), TArray(t2))", try_unite),
        ("(sf==TFunc(sa, sr), df==TFunc(da, dr))", try_unite_funcs),
        ("(src==TData(a, ats), dest==TData(b, bts))", try_unite_datas),
        ("(src==TPrim(sp), dest==TPrim(dp))", try_unite_prims),
        ("(TVoid(), TVoid())", nop),
        ("_", lambda: fail("type mismatch")))

def typecheck(src, dest):
    in_env(UNIFYCTXT, (src, dest), lambda: try_unite(src, dest))

def check(e):
    typecheck(env(CHECK), e)

def pat_tuple(ps):
    ts = match(env(CHECK), "TTuple(ps)")
    for p, t in ezip(ps, ts):
        in_env(CHECK, t, lambda: _check_pat(p))

def pat_var(v):
    check(extrinsic(TypeOf, v))

def pat_capture(v, p):
    pat_var(v)
    _check_pat(p)

def pat_ctor(pat, ctor, args):
    ctorT = extrinsic(TypeOf, ctor)
    fieldTs, dt = match(ctorT, ("TFunc(fs, dt)", tuple2))
    if has_extrinsic(Instantiation, pat):
        inst = extrinsic(Instantiation, pat)
        ctorT = checked_subst(inst, ctorT)
        paramTs, pdt = match(ctorT, ("TFunc(ps, pdt)", tuple2))
        check(pdt)
        # Check whether each field is affected by instantiation or not
        for arg, (fieldT, paramT) in ezip(args, ezip(fieldTs, paramTs)):
            if subst_affects(inst, fieldT):
                # both these types are pretty obvious from the context...
                typecast = (fieldT, paramT)
                add_extrinsic(TypeCast, arg, typecast)
            in_env(CHECK, paramT, lambda: _check_pat(arg))
    else:
        check(dt)
        for arg, fieldT in ezip(args, fieldTs):
            in_env(CHECK, fieldT, lambda: _check_pat(arg))

def _check_pat(p):
    match(p,
        ("PatInt(_)", lambda: check(TInt())),
        ("PatStr(_)", lambda: check(TStr())),
        ("PatWild()", nop),
        ("PatTuple(ps)", pat_tuple),
        ("PatVar(v)", pat_var),
        ("PatCapture(v, p)", pat_capture),
        ("pat==PatCtor(c, args)", pat_ctor))

def check_pat_as(t, p):
    # bad type, meh
    in_env(CHECK, t, lambda: in_env(EXPRCTXT, p, lambda: _check_pat(p)))

def occurs(typeVar, t):
    return not visit_type_vars(lambda tv: tv is not typeVar, t)

def subst_affects(mapping, t):
    return not visit_type_vars(lambda tv: tv not in mapping, t)

# Make sure the input is sane and non-redundant
def checked_subst(mapping, t):
    for tvar, rt in mapping.iteritems():
        assert not occurs(tvar, rt), "%s occurs in replacement %s" % (tvar, rt)
    unseen = set(mapping)
    assert len(unseen) > 0, "Empty substitution for %s" % (t,)
    def app(st):
        tvar = st.typeVar
        if tvar in mapping:
            st = mapping[tvar]
            if tvar in unseen:
                unseen.remove(tvar)
        return st
    s = map_type_vars(app, t)
    assert len(unseen) == 0, "Typevars %s unused in subst for %s" % (unseen, t)
    return s

def check_binding(bind, binding):
    t = binding_typeof(binding)
    if has_extrinsic(Instantiation, bind):
        newT = checked_subst(extrinsic(Instantiation, bind), t)
        add_extrinsic(TypeCast, bind, (t, newT))
        t = newT
    check(t)

def check_inst_call(e, inst, f, args):
    # Instead of typecasting f, typecast its args backwards
    origT = binding_typeof(match(f, 'Bind(binding)'))
    origArgTs, origRetT = match(origT, ("TFunc(args, ret)", tuple2))
    t = checked_subst(inst, origT)

    # Avoid check_expr_as() here to avoid check_binding(), which would conflict
    typecheck(t, extrinsic(TypeOf, f))

    argTs, retT = match(t, ("TFunc(args, ret)", tuple2))
    if subst_affects(inst, origRetT):
        # XXX this is going to clobber other casts... need to be able to
        # compose them? or do this differently?
        #add_extrinsic(TypeCast, e, (origRetT, retT))
        pass
    check(retT)

    for arg, (origT, newT) in ezip(args, ezip(origArgTs, argTs)):
        if subst_affects(inst, origT):
            # cast back into the field spec type
            add_extrinsic(TypeCast, arg, (newT, origT))
        check_expr_as(newT, arg)

def check_call(e, f, args):
    if has_extrinsic(Instantiation, f):
        check_inst_call(e, extrinsic(Instantiation, f), f, args)
        return
    t = check_expr_as_itself(f)
    argts, rett = match(t, ("TFunc(args, ret)", tuple2))
    check(rett)
    for arg, t in ezip(args, argts):
        check_expr_as(t, arg)

def check_tuplelit(es):
    ts = match(env(CHECK), "TTuple(ts)")
    for t, e in ezip(ts, es):
        check_expr_as(t, e)

def check_listlit(es):
    ts = match(env(CHECK), "TArray(ts)")
    for t, e in ezip(ts, es):
        check_expr_as(t, e)

def check_logic(l, r):
    check_expr_as(TBool(), l)
    check_expr_as(TBool(), r)

def check_ternary(c, t, f):
    check_expr_as(TBool(), c)
    check_same(t)
    check_same(f)

def check_func(f, ps, b):
    ft = extrinsic(TypeOf, f)
    tps, tret = match(ft, ('TFunc(ps, ret)', tuple2))
    in_env(CHECKSCOPE, tret, lambda: check_body(b))

def check_match(m, e, cs):
    et = check_expr_as_itself(e)
    retT = match(env(CHECK), ("TVoid()", Nothing),
                             ("otherwise", Just))
    for c in cs:
        cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))
        check_pat_as(et, cp)
        if isJust(retT):
            check_expr_as(fromJust(retT), ce)
        else:
            check_expr_as_itself(ce)

def check_attr(e, f, ft):
    check(ft)
    t = extrinsic(TypeOf, e)
    check_contains_field(t, f)
    check_expr_as(t, e)

def check_inenv(t, init, f):
    check_expr_as(t, init)
    check_same(f)

def check_getextrinsic(t, node):
    check(t)
    check_expr_as_boxed(node)

def check_hasextrinsic(node):
    check(TBool())
    check_expr_as_boxed(node)

def check_expr_as_boxed(e):
    t = check_expr_as_itself(e)
    assert matches(t, "TData(_, _)"), "Can't add extr to %s" % (nodet,)

def check_expr_as(t, e):
    typecheck(extrinsic(TypeOf, e), t)
    in_env(CHECK, t, lambda: in_env(EXPRCTXT, e, lambda: _check_expr(e)))

def check_expr_as_itself(e):
    t = extrinsic(TypeOf, e)
    in_env(CHECK, t, lambda: in_env(EXPRCTXT, e, lambda: _check_expr(e)))
    return t

def check_same(e):
    typecheck(extrinsic(TypeOf, e), env(CHECK))
    in_env(EXPRCTXT, e, lambda: _check_expr(e))

def _check_expr(e):
    match(e,
        ("IntLit(_)", lambda: check(TInt())),
        ("StrLit(_)", lambda: check(TStr())),
        ("e==Call(f, args)", check_call),
        ("TupleLit(es)", check_tuplelit),
        ("ListLit(es)", check_listlit),
        ("And(l, r) or Or(l, r)", check_logic),
        ("Ternary(c, t, f)", check_ternary),
        ("FuncExpr(f==Func(ps, b))", check_func),
        ("m==Match(p, cs)", check_match),
        ("Attr(e, f==Field(ft))", check_attr),
        ("GetEnv(Env(t))", check),
        ("HaveEnv(_)", lambda: check(TBool())),
        ("InEnv(Env(t), init, f)", check_inenv),
        ("GetExtrinsic(Extrinsic(t), node)", check_getextrinsic),
        ("HasExtrinsic(_, node)", check_hasextrinsic),
        ("ScopeExtrinsic(_, f)", check_same),
        ("bind==Bind(b)", check_binding))

def check_contains_field(t, f):
    # XXX will want to check instantiation
    form = match(t, "TData(form, _)")
    for ctor in form.ctors:
        if f in ctor.fields:
            return
    assert False, "%s is not a field of %s" % (f, t)

def check_lhs_attr(lhs, s, f):
    check(extrinsic(TypeOf, lhs))
    t = check_expr_as_itself(s)
    check_contains_field(t, f)

def _check_lhs(lhs):
    match(lhs,
        ("LhsVar(v)", lambda v: check(extrinsic(TypeOf, v))),
        ("lhs==LhsAttr(s, f)", check_lhs_attr))

def check_lhs_as(t, lhs):
    in_env(CHECK, t, lambda: _check_lhs(lhs))

def check_lhs_as_itself(a):
    t = extrinsic(TypeOf, a)
    check_lhs_as(t, a)
    return t

def check_DT(form):
    dtT = vanilla_tdata(form)
    for ctor in form.ctors:
        ctorT = TFunc([f.type for f in ctor.fields], dtT)
        typecheck(extrinsic(TypeOf, ctor), ctorT)

def destructure_tuple(ps, t):
    ts = match(t, "CTuple(ts)")
    for p, t in ezip(ps, ts):
        destructure_pat(p, t)

def destructure_pat(pat, t):
    match(pat, ("PatVar(v)", lambda v: set_var_ctype(v, t)),
               ("PatTuple(ps)", lambda ps: destructure_tuple(ps, t)))

def check_pat_as_itself(pat):
    t = extrinsic(TypeOf, pat)
    check_pat_as(t, pat)
    return t

def check_defn(pat, e):
    t = check_pat_as_itself(pat)
    check_expr_as(t, e)

def check_assign(a, e):
    t = check_lhs_as_itself(a)
    check_expr_as(t, e)

def check_augassign(a, e):
    check_lhs_as(TInt(), a)
    check_expr_as(TInt(), e)

def check_cond(cases, else_):
    for case in cases:
        check_expr_as(TBool(), case.test)
        check_body(case.body)
    if isJust(else_):
        check_body(fromJust(else_))

def check_while(test, body):
    check_expr_as(TBool(), test)
    check_body(body)

def check_assert(tst, msg):
    check_expr_as(TBool(), tst)
    check_expr_as(TStr(), msg)

def check_return(e):
    check_expr_as(env(CHECKSCOPE), e)

def check_returnnothing():
    assert matches(env(CHECKSCOPE), "TVoid()")

def check_writeextrinsic(t, node, val):
    check_expr_as_boxed(node)
    check_expr_as(t, val)

def check_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(pat, e)", check_defn),
        ("Assign(lhs, e)", check_assign),
        ("AugAssign(_, lhs, e)", check_augassign),
        ("Break() or Continue()", nop),
        ("ExprStmt(e)", check_expr_as_itself),
        ("Cond(cases, elseCase)", check_cond),
        ("While(t, b)", check_while),
        ("Assert(t, m)", check_assert),
        ("Return(e)", check_return),
        ("ReturnNothing()", check_returnnothing),
        ("WriteExtrinsic(Extrinsic(t), node, val, _)", check_writeextrinsic)))

def check_body(body):
    map_(check_stmt, body.stmts)

def check_top_level(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("TopCDecl(_)", nop),
        ("TopDT(form)", check_DT),
        ("TopEnv(_)", nop),
        ("TopDefn(pat, e)", check_defn),
        ("TopExtrinsic(_)", nop)))

def check_compilation_unit(unit):
    map_(check_top_level, unit.tops)

def check_types(root):
    casts = {}
    capture_extrinsic(TypeCast, casts,
        lambda: check_compilation_unit(root)
    )
    return casts

def in_check_env(func):
    return scope_extrinsic(TypeCast, func)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
