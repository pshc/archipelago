#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from globs import TypeOf

CHECKSCOPE = new_env('CHECKSCOPE', Result)

CHECK = new_env('CHECK', Type)

def unification_failure(src, dest, msg):
    desc = fmtcol("^DG^Couldn't unify^N {0} {1!r}\n^DG^with^N {2} {3!r}",
            type(src), src, type(dest), dest)
    assert False, with_context(desc, msg)

def try_unite_tuples(src, list1, dest, list2):
    for s, d in ezip(list1, list2):
        try_unite(s, d)

def try_unite_funcs(sf, sargs, sret, smeta, df, dargs, dret, dmeta):
    try_unite_tuples(sf, sargs, df, dargs)
    try_unite_results(sf, sret, df, dret)
    if not metas_equal(smeta, dmeta):
        unification_failure(sf, df, "conflicting func metas")

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
        ("(sf==TFunc(sa, sr, sm), df==TFunc(da, dr, dm))", try_unite_funcs),
        ("(src==TData(a, ats), dest==TData(b, bts))", try_unite_datas),
        ("(src==TPrim(sp), dest==TPrim(dp))", try_unite_prims),
        ("_", lambda: fail("type mismatch")))

def try_unite_results(t1, a, t2, b):
    match((a, b), ("(Ret(at), Ret(bt))", try_unite),
                  ("(Void(), Void())", nop),
                  ("(Bottom(), Bottom())", nop),
                  ("_", lambda: unification_failure(t1, t2,
                                "conflicting result types")))

def typecheck(src, dest):
    in_env(UNIFYCTXT, (src, dest), lambda: try_unite(src, dest))

def check(dest):
    typecheck(env(CHECK), dest)

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
    fieldTs, dt = match(ctorT, ("TFunc(fs, Ret(dt), _)", tuple2))
    if has_extrinsic(Instantiation, pat):
        inst = extrinsic(Instantiation, pat)
        ctorT = checked_subst(inst, ctorT)
        paramTs, pdt = match(ctorT, ("TFunc(ps, Ret(pdt), _)", tuple2))
        check(pdt)
        # Check whether each field is affected by instantiation or not
        for arg, (fieldT, paramT) in ezip(args, ezip(fieldTs, paramTs)):
            _ = maybe_typecast(inst, arg, fieldT, paramT)
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

def add_typecast(e, src, dest):
    if match((src, dest), ('(TData(a, _), TData(b, _))', lambda a, b: a is b),
                          ('_', lambda: False)):
        # LLVM repr doesn't distinguish this case, so don't bother
        return
    add_extrinsic(TypeCast, e, (src, dest))

def maybe_typecast(inst, e, fromT, toT):
    if not subst_affects(inst, fromT):
        return False
    if env(GENOPTS).dumpInsts:
        print fmtcol('^Blue^cast ^N{0} ^Blue^to^N {1}', fromT, toT)
    add_typecast(e, fromT, toT)
    return True

def maybe_typecast_reversed(inst, e, fromT, toT):
    if not subst_affects(inst, toT):
        return False
    if env(GENOPTS).dumpInsts:
        print fmtcol('^LightBlue^rcast ^N{0} ^LightBlue^to^N {1}', fromT, toT)
    add_typecast(e, fromT, toT)
    return True

def check_bind(bind, target):
    t = extrinsic(TypeOf, target)
    if has_extrinsic(Instantiation, bind):
        newT = checked_subst(extrinsic(Instantiation, bind), t)
        add_typecast(bind, t, newT)
        t = newT
    check(t)

def check_inst_call(e, inst, f, args):
    # Instead of typecasting f, typecast its args backwards
    origT = extrinsic(TypeOf, f.target)
    origArgTs, origResult = match(origT, ("TFunc(args, res, _)", tuple2))
    t = checked_subst(inst, origT)

    # Avoid check_expr_as() here to avoid check_bind(), which would conflict
    typecheck(t, extrinsic(TypeOf, f))

    argTs, result = match(t, ("TFunc(args, result, _)", tuple2))

    for arg, (origT, newT) in ezip(args, ezip(origArgTs, argTs)):
        _ = maybe_typecast_reversed(inst, arg, newT, origT)
        check_expr_as(newT, arg)

    if matches(result, "Ret(_)"):
        _ = maybe_typecast(inst, e, origResult.type, result.type)
        check(result.type)

    return result

def check_call(e, f, args):
    if has_extrinsic(Instantiation, f):
        res = check_inst_call(e, extrinsic(Instantiation, f), f, args)
        assert matches(res, "Ret(_)")
    else:
        t = check_expr_as_itself(f)
        argts, result = match(t, ("TFunc(args, res, _)", tuple2))
        assert matches(result, "Ret(_)")
        check(result.type)
        for arg, t in ezip(args, argts):
            check_expr_as(t, arg)

def check_void_call(e, f, args):
    if has_extrinsic(Instantiation, f):
        res = check_inst_call(e, extrinsic(Instantiation, f), f, args)
        assert not matches(res, "Ret(_)")
    else:
        t = check_expr_as_itself(f)
        argts, result = match(t, ("TFunc(args, res, _)", tuple2))
        assert not matches(result, "Ret(_)")
        for arg, t in ezip(args, argts):
            check_expr_as(t, arg)

def check_tuplelit(es):
    ts = match(env(CHECK), "TTuple(ts)")
    for t, e in ezip(ts, es):
        check_expr_as(t, e)

def check_listlit(es):
    t = match(env(CHECK), "TArray(t)")
    for e in es:
        check_expr_as(t, e)

def check_logic(l, r):
    check_expr_as(TBool(), l)
    check_expr_as(TBool(), r)

def check_ternary(c, t, f):
    check_expr_as(TBool(), c)
    # void return not OK
    check_same(t)
    check_same(f)

def check_func(f):
    ft = extrinsic(TypeOf, f)
    tps, tresult = match(ft, ('TFunc(ps, result, _)', tuple2))
    for p, tp in ezip(f.params, tps):
        typecheck(extrinsic(TypeOf, p), tp)
    in_env(CHECKSCOPE, tresult, lambda: check_body(f.body))

def check_match(m, e, cs):
    et = check_expr_as_itself(e)
    retT = env(CHECK)
    for c in cs:
        cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))
        check_pat_as(et, cp)
        check_expr_as(retT, ce)

def check_void_match(m, e, cs):
    et = check_expr_as_itself(e)
    for c in cs:
        cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))
        check_pat_as(et, cp)
        check_expr_as_itself(ce)

def check_attr(e, f, ft):
    check(ft)
    t = extrinsic(TypeOf, e)
    check_contains_field(t, f)
    check_expr_as(t, e)

def check_inenv(t, init, f):
    check_expr_as(t, init)
    check_same(f)

def check_void_inenv(t, init, f):
    check_expr_as(t, init)
    check_voidexpr(f)

def check_getextrinsic(t, node):
    check(t)
    check_expr_as_boxed(node)

def check_hasextrinsic(node):
    check(TBool())
    check_expr_as_boxed(node)

def check_expr_as_boxed(e):
    t = check_expr_as_itself(e)
    assert matches(t, "TData(_, _)"), "Can't add extr to %s" % (nodet,)
    opts = t.data.opts
    assert not opts.valueType, "Can't add extr to value-DT %s" % (nodet,)

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
        ("Lit(lit)", lambda lit: check(lit_type(lit))),
        ("e==Call(f, args)", check_call),
        ("TupleLit(es)", check_tuplelit),
        ("ListLit(es)", check_listlit),
        ("And(l, r) or Or(l, r)", check_logic),
        ("Ternary(c, t, f)", check_ternary),
        ("FuncExpr(f)", check_func),
        ("m==Match(p, cs)", check_match),
        ("Attr(e, f==Field(ft))", check_attr),
        ("GetEnv(Env(t))", check),
        ("HaveEnv(_)", lambda: check(TBool())),
        ("InEnv(Env(t), init, f)", check_inenv),
        ("GetExtrinsic(Extrinsic(t), node)", check_getextrinsic),
        ("HasExtrinsic(_, node)", check_hasextrinsic),
        ("ScopeExtrinsic(_, f)", check_same),
        ("bind==Bind(target)", check_bind))

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
        ctorT = TFunc([f.type for f in ctor.fields], Ret(dtT), basic_meta())
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

def check_cond(cases):
    for case in cases:
        check_expr_as(TBool(), case.test)
        check_body(case.body)

def check_while(test, body):
    check_expr_as(TBool(), test)
    check_body(body)

def check_assert(tst, msg):
    check_expr_as(TBool(), tst)
    check_expr_as(TStr(), msg)

def check_return(e):
    check_expr_as(env(CHECKSCOPE).type, e)

def check_returnnothing():
    assert not matches(env(CHECKSCOPE), "Ret(_)")

def check_writeextrinsic(t, node, val):
    check_expr_as_boxed(node)
    check_expr_as(t, val)

def check_voidexpr(e):
    match(e,
        ("call==VoidCall(f, args)", check_void_call),
        ("VoidInEnv(Env(t), init, e)", check_void_inenv))

def check_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(pat, e)", check_defn),
        ("Assign(lhs, e)", check_assign),
        ("AugAssign(_, lhs, e)", check_augassign),
        ("Break() or Continue()", nop),
        ("Cond(cases)", check_cond),
        ("While(t, b)", check_while),
        ("Assert(t, m)", check_assert),
        ("Return(e)", check_return),
        ("ReturnNothing()", check_returnnothing),
        ("WriteExtrinsic(Extrinsic(t), node, val, _)", check_writeextrinsic),
        ("VoidStmt(e)", check_voidexpr)))

def check_body(body):
    map_(check_stmt, body.stmts)

def check_top_func(var, func):
    typecheck(extrinsic(TypeOf, func), extrinsic(TypeOf, var))
    check_func(func)

def check_module_decls(decls):
    for dt in decls.dts:
        in_env(STMTCTXT, dt, lambda: check_DT(dt))
    for lit in decls.lits:
        in_env(STMTCTXT, lit, lambda:
                typecheck(lit_type(lit.literal), extrinsic(TypeOf, lit.var)))

def check_compilation_unit(unit):
    for f in unit.funcs:
        in_env(STMTCTXT, f, lambda: check_top_func(f.var, f.func))

def check_types(decl_mod, defn_mod):
    def go():
        check_module_decls(decl_mod.root)
        check_compilation_unit(defn_mod.root)
    casts = {}
    capture_extrinsic(TypeCast, casts, go)
    return casts

def in_check_env(func):
    return scope_extrinsic(TypeCast, func)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
