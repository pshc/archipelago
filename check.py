#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from globs import TypeOf, ResultOf

CheckScope = DT('CheckScope', ('result', Result),
                              ('envsPresent', set(['*Env'])))
CHECKSCOPE = new_env('CHECKSCOPE', CheckScope)

CHECK = new_env('CHECK', Type)
CHECKRESULT = new_env('CHECKRESULT', Result)

def unification_failure(src, dest, msg):
    desc = fmtcol("^DG^Couldn't unify^N {0} {1!r}\n^DG^with^N {2} {3!r}",
            type(src), src, type(dest), dest)
    assert False, with_context(desc, msg)

def try_unite_tuples(src, list1, dest, list2):
    for s, d in ezip(list1, list2):
        try_unite(s, d)

def try_unite(src, dest):
    fail = lambda m: unification_failure(src, dest, m)
    m = match((src, dest))
    if m("(TVar(stv), TVar(dtv))"):
        if m.stv is not m.dtv:
            unification_failure(src, dest, "typevars")
    elif m("(TTuple(t1), TTuple(t2))"):
        try_unite_tuples(src, m.t1, dest, m.t2)
    elif m("(TArray(t1, k1), TArray(t2, k2))"):
        try_unite(m.t1, m.t2)
        if not array_kinds_equal(m.k1, m.k2):
            unification_failure(src, dest, "array kinds")
    elif m("(TFunc(sa, sr, sm), TFunc(da, dr, dm))"):
        try_unite_tuples(src, m.sa, dest, m.da)
        try_unite_results(src, m.sr, dest, m.dr)
        if not metas_equal(m.sm, m.dm):
            unification_failure(src, dest, "conflicting func metas")
    elif m("(TData(a, ats), TData(b, bts))"):
        if m.a is not m.b:
            unification_failure(src, dest, "mismatched datatypes")
        assert len(m.ats) == len(m.a.tvars), "Wrong %s typevar count" % (m.a,)
        for at, bt in ezip(m.ats, m.bts):
            try_unite(at, bt)
    elif m("(TPrim(sp), TPrim(dp))"):
        if not prim_equal(m.sp, m.dp):
            unification_failure(src, dest, "primitive types")
    elif m("(TWeak(a), TWeak(b))"):
        try_unite(m.a, m.b)
    elif m("(TWeak(a), _)"):
        try_unite(m.a, dest)
    elif m("(_, TWeak(b))"):
        try_unite(src, m.b)
    else:
        fail("type mismatch")

def try_unite_results(t1, a, t2, b):
    m = match((a, b))
    if m("(Ret(at), Ret(bt))"):
        try_unite(m.at, m.bt)
    elif not results_equal(a, b):
        unification_failure(t1, t2, "conflicting result types")

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

    if has_extrinsic(TypeCast, e):
        # This is backwards
        oldSrc, oldDest = extrinsic(TypeCast, e)
        typecheck(dest, oldSrc)
        update_extrinsic(TypeCast, e, (src, oldDest))
    else:
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

def check_call_envs(e, meta):
    present = env(CHECKSCOPE).envsPresent
    for environ in meta.requiredEnvs:
        assert environ in present, "%s requires env %s" % (f, environ)

def check_inst_call(e, inst, f, args):
    # Instead of typecasting f, typecast its args backwards
    origT = extrinsic(TypeOf, f.target)
    origArgTs, origResult = match(origT, ("TFunc(args, res, _)", tuple2))
    t = checked_subst(inst, origT)

    # Avoid check_expr_as() here to avoid check_bind(), which would conflict
    typecheck(t, extrinsic(TypeOf, f))

    argTs, result, meta = match(t, ("TFunc(args, result, meta)", tuple3))

    # XXX maybe codegen
    # don't bother casting x to `a in Just(x)
    # this is ugly... consider rewriting this cast instead in MaybeConverter?
    skipCasts = Nullable.isMaybe(f.target)

    for arg, (origT, newT) in ezip(args, ezip(origArgTs, argTs)):
        if not skipCasts:
            _ = maybe_typecast_reversed(inst, arg, newT, origT)
        check_expr_as(newT, arg)

    if matches(result, "Ret(_)"):
        _ = maybe_typecast(inst, e, origResult.type, result.type)
        check(result.type)

    check_call_envs(e, meta)
    return result

def check_straight_call(e, f, args):
    t = check_expr_as_itself(f)
    argTs, result, meta = match(t, ("TFunc(args, result, meta)", tuple3))
    for arg, t in ezip(args, argTs):
        check_expr_as(t, arg)

    if matches(result, "Ret(_)"):
        check(result.type)

    check_call_envs(e, meta)
    return result

def check_call(e, f, args):
    if has_extrinsic(Instantiation, f):
        res = check_inst_call(e, extrinsic(Instantiation, f), f, args)
    else:
        res = check_straight_call(e, f, args)
    assert matches(res, "Ret(_)")

def check_void_call(e, f, args):
    if has_extrinsic(Instantiation, f):
        res = check_inst_call(e, extrinsic(Instantiation, f), f, args)
    else:
        res = check_straight_call(e, f, args)
    assert results_equal(res, env(CHECKRESULT))

def check_tuplelit(es):
    ts = match(env(CHECK), "TTuple(ts)")
    for t, e in ezip(ts, es):
        check_expr_as(t, e)

# TODO should be called on every array type in the AST (not just literals)
def check_array_type(arrayT):
    t, kind = match(arrayT, "TArray(t, kind)")
    # simple check for now
    isRaw = matches(kind, "ARaw()")
    m = match(t)
    if m("TPrim(prim)"):
        # includes PStr pffffft
        assert isRaw, "Unboxed type %s in non-raw array" % (m.prim,)
    else:
        assert not isRaw, "Boxed type %s  in raw array" % (t,)
    return t

def check_listlit(es):
    t = env(CHECK)
    elemT = check_array_type(t)
    for e in es:
        check_expr_as(elemT, e)

def check_logic(l, r):
    check_expr_as(TBool(), l)
    check_expr_as(TBool(), r)

def check_ternary(c, t, f):
    check_expr_as(TBool(), c)
    # void return not OK
    check_same(t)
    check_same(f)

def check_func(var, f):
    ft = extrinsic(TypeOf, var)
    for p, tp in ezip(f.params, ft.paramTypes):
        typecheck(extrinsic(TypeOf, p), tp)
    scope = CheckScope(ft.result, set(ft.meta.requiredEnvs))
    in_env(CHECKSCOPE, scope, lambda: check_body(f.body))

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

def check_inenv(environ, init, f):
    check_expr_as(environ.type, init)
    present = env(CHECKSCOPE).envsPresent
    introduced = environ not in present
    if introduced:
        present.add(environ)
    check_same(f)
    if introduced:
        present.remove(environ)

def check_void_inenv(environ, init, f):
    check_expr_as(environ.type, init)
    present = env(CHECKSCOPE).envsPresent
    introduced = environ not in present
    if introduced:
        present.add(environ)
    check_voidexpr(f)
    if introduced:
        present.remove(environ)

# TEMP
def check_makectx(environ, init):
    check(t_DT(Env))
    check_expr_as(environ.type, init)

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
        ("e==FuncExpr(f)", check_func),
        ("m==Match(p, cs)", check_match),
        ("Attr(e, f==Field(ft))", check_attr),
        ("GetEnv(Env(t))", check),
        ("HaveEnv(_)", lambda: check(TBool())),
        ("InEnv(environ, init, f)", check_inenv),
        ("MakeCtx(environ, init)", check_makectx),
        ("GetExtrinsic(Extrinsic(t), node)", check_getextrinsic),
        ("HasExtrinsic(_, node)", check_hasextrinsic),
        ("ScopeExtrinsic(_, f)", check_same),
        ("bind==Bind(target)", check_bind))

def check_contains_field(t, f):
    # XXX will want to check instantiation
    form = match(t, "TData(form, _) or TWeak(TData(form, _))")
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
        typecheck(extrinsic(TypeOf, ctor), ctor_type(ctor, dtT))

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

def check_block_match(p, cs):
    et = check_expr_as_itself(p)
    for c in cs:
        cp, cb = match(c, ("MatchCase(cp, cb)", tuple2))
        check_pat_as(et, cp)
        check_body(cb)

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
    check_expr_as(env(CHECKSCOPE).result.type, e)

def check_returnnothing():
    assert not matches(env(CHECKSCOPE).result, "Ret(_)")

def check_writeextrinsic(t, node, val):
    check_expr_as_boxed(node)
    check_expr_as(t, val)

def check_voidexpr(e):
    match(e,
        ("call==VoidCall(f, args)", check_void_call),
        ("VoidInEnv(environ, init, e)", check_void_inenv))

def check_voidstmt(s, e):
    result = extrinsic(ResultOf, s)
    assert not matches(result, "Ret(_)")
    in_env(CHECKRESULT, result, lambda: check_voidexpr(e))

def check_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(pat, e)", check_defn),
        ("Assign(lhs, e)", check_assign),
        ("AugAssign(_, lhs, e)", check_augassign),
        ("Break() or Continue()", nop),
        ("BlockMatch(p, cs)", check_block_match),
        ("Cond(cases)", check_cond),
        ("While(t, b)", check_while),
        ("Assert(t, m)", check_assert),
        ("Return(e)", check_return),
        ("ReturnNothing()", check_returnnothing),
        ("WriteExtrinsic(Extrinsic(t), node, val, _)", check_writeextrinsic),
        ("s==VoidStmt(e)", check_voidstmt)))

def check_body(body):
    map_(check_stmt, body.stmts)

def check_module_decls(decls):
    for dt in decls.dts:
        in_env(STMTCTXT, dt, lambda: check_DT(dt))
    for lit in decls.lits:
        in_env(STMTCTXT, lit, lambda:
                typecheck(lit_type(lit.literal), extrinsic(TypeOf, lit.var)))

def check_compilation_unit(unit):
    for f in unit.funcs:
        in_env(STMTCTXT, f, lambda: check_func(f.var, f.func))

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
