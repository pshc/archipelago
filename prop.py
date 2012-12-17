#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from globs import TypeOf
import vat

INPAT = new_env('INPAT', '*Type')

PropScope = DT('PropScope', ('result', 'Result(CType)'),
                            ('localVars', {'*Var': 'CType'}))

PROPSCOPE = new_env('PROPSCOPE', 'PropScope')

PROPTOP = new_env('PROPTOP', '*TopFunc')

PendingInst = new_extrinsic('PendingInst', {'*TypeVar': 'CType'})

def in_new_scope(result, f):
    localVars = {}
    if have_env(PROPSCOPE):
        localVars = env(PROPSCOPE).localVars.copy()
    new_scope = PropScope(result, localVars)
    return in_env(PROPSCOPE, new_scope, f)

MetaCell, Free, InstVar, Mono, Subst = ADT('MetaCell',
    'Free', ('typeVar', 'Maybe(TypeVar)'),
    'InstVar', ('origTypeVar', '*TypeVar'),
    'Mono',
    'Subst', ('type', 'CType'))

# instantiated types

CType, C, CMeta = ADT(('CType', Type),
        'CMeta', ('cell', MetaCell))

CType.__repr__ = cyclic_check_type_repr

PendingType = new_extrinsic('PendingType', CType)

def CInt(): return C.TPrim(PInt())
def CFloat(): return C.TPrim(PFloat())
def CBool(): return C.TPrim(PBool())
def CStr(): return C.TPrim(PStr())

InstInfo = DT('InstInfo', ('metas', {TypeVar: CType}),
                          ('hintLookup', {TypeVar: Type}))
INST = new_env('INST', {TypeVar: Type})

# direct transformation to C* (hacky reuse of _inst_type)
SUBST = new_env('SUBST', {'*TypeVar': Type})

def fresh():
    return CMeta(Free(Nothing()))

def fresh_from(tv):
    return CMeta(InstVar(tv))

def fresh_monotype():
    return CMeta(Mono())

def inst_tvar(tv):
    if have_env(SUBST):
        return env(SUBST).get(tv, C.TVar(tv))
    inst = env(INST)
    t = inst.hintLookup.get(tv)
    if t is not None:
        return ctype(t)
    else:
        meta = inst.metas.get(tv)
        if meta is None:
            inst.metas[tv] = meta = fresh_from(tv)
        return meta

def inst_tdata(dt, ts):
    assert len(ts) == len(dt.tvars)
    return C.TData(dt, map(_inst_type, ts))

def _inst_type(s):
    return match(s,
        ('TVar(tv)', inst_tvar),
        ('TPrim(p)', C.TPrim),
        ('TTuple(ts)', lambda ts: C.TTuple(map(_inst_type, ts))),
        ('TFunc(ps, r, meta)', lambda ps, r, meta:
                C.TFunc(map(_inst_type, ps), _inst_result(r), copy_meta(meta))),
        ('TData(dt, ts)', inst_tdata),
        ('TArray(t)', lambda t: C.TArray(_inst_type(t))),
        ('TWeak(t)', lambda t: C.TWeak(_inst_type(t))))

def _inst_result(r):
    return match(r, ('Ret(t)', lambda t: Ret(_inst_type(t))),
                    ('Void()', Void),
                    ('Bottom()', Bottom))

def instantiate_type(site, t):
    insts = {}
    hints = extrinsic(InstMap, site) if has_extrinsic(InstMap, site) else {}
    ct = in_env(INST, InstInfo(insts, hints), lambda: _inst_type(t))
    if len(insts) > 0:
        add_extrinsic(PendingInst, site, insts)
    return ct

def ctype(t):
    return in_env(SUBST, {}, lambda: _inst_type(t))

def ctype_replaced(t, substs):
    return in_env(SUBST, substs, lambda: _inst_type(t))

def gen_tdata(dt, ats):
    assert len(ats) == len(dt.tvars)
    return TData(dt, [_gen_type(at) for at in ats])

def capture_free(f):
    tvar = TypeVar()
    add_extrinsic(Name, tvar, 'free')
    f.typeVar = Just(tvar)
    top = env(PROPTOP)
    if not has_extrinsic(TypeVars, top):
        add_extrinsic(TypeVars, top, [])
    extrinsic(TypeVars, top).append(tvar)
    return TVar(tvar)

def free_monotype():
    assert False, with_context("Can't infer param type", "monotypes only")

def _gen_type(s):
    return match(s,
        ('TVar(tv)', TVar),
        ('TPrim(p)', TPrim),
        ('TTuple(ts)', lambda ts: TTuple(map(_gen_type, ts))),
        ('TFunc(ps, r, meta)', lambda ps, r, meta:
                TFunc(map(_gen_type, ps), _gen_result(r), copy_meta(meta))),
        ('TData(dt, ts)', gen_tdata),
        ('TArray(t)', lambda t: TArray(_gen_type(t))),
        ('TWeak(t)', lambda t: TWeak(_gen_type(t))),
        ('CMeta(Free(Just(tvar)))', TVar),
        ('CMeta(f==Free(Nothing()))', capture_free),
        ('CMeta(InstVar(tv))', TVar),
        ('CMeta(Mono())', free_monotype),
        ('CMeta(Subst(s))', _gen_type))

def _gen_result(r):
    return match(r, ('Ret(t)', lambda t: Ret(_gen_type(t))),
                    ('Void()', Void),
                    ('Bottom()', Bottom))

def finalize_type(t):
    return _gen_type(t)

def unification_failure(src, dest, msg):
    desc = fmtcol("^DG^Couldn't unify^N {0} {1!r}\n^DG^with^N {2} {3!r}",
            type(src), src, type(dest), dest)
    assert False, with_context(desc, msg)

def try_unite_tuples(src, list1, dest, list2):
    for s, d in ezip(list1, list2):
        try_unite(s, d)

def try_unite_results(t1, a, t2, b):
    match((a, b), ("(Ret(at), Ret(bt))", try_unite),
                  ("(Void(), Void())", nop),
                  ("(Bottom(), Bottom())", nop),
                  ("_", lambda: unification_failure(t1, t2,
                                "conflicting result types")))

def try_unite_two_metas(src, dest):
    if src is dest:
        return
    srcType = match(src.cell.meta, ('Subst(t)', Just), ('_', Nothing))
    destType = match(dest.cell.meta, ('Subst(t)', Just), ('_', Nothing))
    if isJust(srcType) and isJust(destType):
        try_unite(fromJust(srcType), fromJust(destType))
    elif isJust(srcType):
        # XXX ought to narrow properly
        dest.cell = Subst(src)
    else:
        src.cell = Subst(dest)

def set_meta_subst(src, dest):
    src.cell = Subst(dest)

def copy_mono_subst(src, dest):
    # mono modifier may be too viral?
    dest.cell = Mono()
    src.cell = Subst(dest)

def try_unite_meta(m, cell, dest):
    m.cell = Subst(dest)
    if isJust(mcell.type):
        try_unite(fromJust(mcell.type), dest)
    else:
        # zonking dest might be a good idea
        mcell.type = Just(dest)

def try_unite_meta_backwards(dest, meta):
    # XXX ought to narrow properly
    try_unite(meta, dest)

def try_unite(src, dest):
    if src is dest:
        return
    fail = lambda m: unification_failure(src, dest, m)

    m = match((src, dest))
    if m('CMeta(Subst(s), CMeta(Subst(d)))'):
        try_unite(m.s, m.d)

        # two free vars
    elif m("(CMeta(Free(_)), CMeta(Free(_) or InstVar(_) or Mono()))"):
        set_meta_subst(src, dest)
    elif m("(CMeta(InstVar(_)), CMeta(Free(_) or InstVar(_) or Mono()))"):
        set_meta_subst(src, dest)
    elif m("(CMeta(Mono()), CMeta(Mono()))"):
        set_meta_subst(src, dest)
    elif m("(CMeta(Mono()), CMeta(Free(_) or InstVar(_)))"):
        copy_mono_subst(src, dest)

        # free -> some type (direct unification)
    elif m("(CMeta(Subst(src)), _)"):
        try_unite(m.src, dest)
    elif m("(CMeta(Mono()), TVar(_))"):
        fail("Can't infer polytype for func params/ret; provide annot")
    elif m("(CMeta(_), _)"):
        set_meta_subst(src, dest)

        # some type -> free (possible generalization)
    elif m("(_, CMeta(_))"):
        # XXX ought to narrow properly
        try_unite(dest, src)

    elif m("(TWeak(a), TWeak(b))"):
        try_unite(m.a, m.b)
    elif m("(TWeak(a), _)"):
        try_unite(m.a, dest)
    elif m("(_, TWeak(b))"):
        try_unite(src, m.b)

    elif m("(TVar(stv), TVar(dtv))"):
        if m.stv is not m.dtv:
            unification_failure(src, dest, "typevars")
    elif m("(TTuple(t1), TTuple(t2))"):
        try_unite_tuples(src, m.t1, dest, m.t2)
    elif m("(TArray(t1), TArray(t2))"):
        try_unite(m.t1, m.t2)
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
    else:
        fail("type mismatch")

def unify(src, dest):
    in_env(UNIFYCTXT, (src, dest), lambda: try_unite(src, dest))

def unify_m(t):
    unify(env(INPAT), t)

def unify_results(src, dest):
    in_env(UNIFYCTXT, (src, dest),
            lambda: try_unite_results(src, src, dest, dest))

def set_type(e, t):
    assert isinstance(t, Type), "%s is not a type" % (t,)
    add_extrinsic(TypeOf, e, t)

def set_var_ctype(v, ct):
    if have_env(PROPSCOPE):
        env(PROPSCOPE).localVars[v] = ct
    add_extrinsic(PendingType, v, ct)

def pat_tuple(ps):
    ts = match(env(INPAT), "TTuple(ps)")
    for p, t in ezip(ps, ts):
        in_env(INPAT, t, lambda: _prop_pat(p))

def pat_var(v):
    set_var_ctype(v, env(INPAT))

def pat_capture(v, p):
    pat_var(v)
    _prop_pat(p)

def pat_ctor(ref, ctor, args):
    ctorT = instantiate_type(ref, extrinsic(TypeOf, ctor))
    fieldTs, dt = match(ctorT, ("TFunc(fs, Ret(dt), _)", tuple2))
    unify_m(dt)
    for arg, fieldT in ezip(args, fieldTs):
        in_env(INPAT, fieldT, lambda: _prop_pat(arg))

def prop_pat(t, p):
    # bad type, meh
    in_env(EXPRCTXT, p, lambda: in_env(INPAT, t, lambda: _prop_pat(p)))

def _prop_pat(p):
    match(p,
        ("PatInt(_)", lambda: unify_m(CInt())),
        ("PatStr(_)", lambda: unify_m(CStr())),
        ("PatWild()", nop),
        ("PatTuple(ps)", pat_tuple),
        ("PatVar(v)", pat_var),
        ("PatCapture(v, p)", pat_capture),
        ("p==PatCtor(c, args)", pat_ctor))
    add_extrinsic(PendingType, p, env(INPAT))

def prop_bind(b, target):
    m = match(Bindable.asLocalVar(target))
    if m('Just(v)'):
        return prop_local_var(m.v)
    else:
        return instantiate_type(b, extrinsic(TypeOf, target))

def prop_local_var(v):
    return env(PROPSCOPE).localVars[v]

def prop_lit(lit):
    return ctype(lit_type(lit))

def prop_listlit(es):
    if len(es) == 0:
        return C.TArray(fresh())
    else:
        t = prop_expr(es[0])
        for e in es[1:]:
            consume_value_as(t, e)
        return C.TArray(t)

def prop_call_result(call, f, s):
    ft = prop_expr(f)
    argts = map(prop_expr, s)

    # TEMP: resolve numeric operator overload
    if 1 <= len(argts) <= 2 and matches(argts[0], "TPrim(PFloat())") and \
                matches(f, "Bind(_)"):
        newf = overload_num_call(f.target)
        if newf:
            f = newf
            call.func = f
            ft = prop_expr(f)

    paramTypes, result = match(ft, ("TFunc(ps, res, _)", tuple2))
    for arg, param in ezip(argts, ft.paramTypes):
        unify(arg, param)
    return result

def prop_call(call, f, s):
    result = prop_call_result(call, f, s)
    assert matches(result, "Ret(_)"), "%s is void" % (call,)
    return result.type

def overload_num_call(f):
    if matches(f, "key('negate')"):
        return E.Bind(BUILTINS['fnegate'])

def prop_logic(l, r):
    consume_value_as(CBool(), l)
    consume_value_as(CBool(), r)
    return CBool()

def prop_ternary(c, t, f):
    consume_value_as(CBool(), c)
    tt = prop_expr(t)
    tf = prop_expr(f)
    unify(tt, tf)
    return tf

def infer_func(f, ps, b):
    result = Ret(fresh_monotype())
    def inside_func():
        localVars = env(PROPSCOPE).localVars
        pts = []
        for p in ps:
            assert p not in localVars
            pt = fresh_monotype()
            set_var_ctype(p, pt)
            pts.append(pt)

        meta = plain_meta([plain_param_meta() for p in pts])
        cft = C.TFunc(pts, result, meta)
        # lambdas can't recurse, but this (sort of thing) would be nice
        #localVars[f] = cft
        prop_body(b)

        return cft
    return in_new_scope(result, inside_func)

def prop_func_expr(typeHolder, f, ps, b):
    if not has_extrinsic(TypeOf, typeHolder):
        return infer_func(f, ps, b)
    ft = extrinsic(TypeOf, typeHolder)
    cft = ctype(ft)
    tps, result = match(cft, ('TFunc(ps, result, _)', tuple2))
    def inside_func_scope():
        for p, ctp in ezip(ps, tps):
            set_var_ctype(p, ctp)
        prop_body(b)
        return cft
    return in_new_scope(result, inside_func_scope)

def prop_match(m, e, cs):
    et = prop_expr(e)
    overallResult = Nothing()
    for c in cs:
        cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))
        def prop_case():
            prop_pat(et, cp)
            thisReturn = prop_expr(ce)
            overallResult = env(PROPSCOPE).result
            # todo: void results
            if isJust(overallResult):
                unify(thisReturn, fromJust(overallResult).type)
            else:
                overallResult = Just(Ret(thisReturn))
            return overallResult
        overallResult = in_new_scope(overallResult, prop_case)
    return match(overallResult, "Just(Ret(t))")

def prop_block_match(e, cs):
    et = prop_expr(e)
    overallResult = Nothing()
    for c in cs:
        cp, cb = match(c, ("MatchCase(cp, cb)", tuple2))
        def prop_case():
            prop_pat(et, cp)
            prop_body(cb)
        in_new_scope(overallResult, prop_case)

def prop_attr(e, s, f):
    t = prop_expr(s)
    # TEMP: resolve the field name now that we have type info
    e.field = resolve_field_by_name(t, f)
    return resolve_field_type(t, e.field.type)

def prop_inenv(t, init, f):
    consume_value_as(ctype(t), init)
    return prop_expr(f)

# TEMP
def prop_makectx(t, init):
    consume_value_as(ctype(t), init)
    return t_DT(Env)

def prop_getextrinsic(e, extr, node):
    t = prop_expr(node)
    assert matches(t, "TData(_, _)"), "Can't get extr from %s" % (nodet,)
    return instantiate_type(e, extr.type)

def prop_hasextrinsic(e, node):
    t = prop_expr(node)
    assert matches(t, "TData(_, _)"), "Can't check for extr from %s" % (nodet,)
    return CBool()

def prop_expr(e):
    return in_env(EXPRCTXT, e, lambda: _prop_expr(e))

def _prop_expr(e):
    rt = match(e,
        ("Lit(lit)", prop_lit),
        ("TupleLit(ts)", lambda ts: C.TTuple(map(prop_expr, ts))),
        ("ListLit(ss)", prop_listlit),
        ("call==Call(f, s)", prop_call),
        ("And(l, r) or Or(l, r)", prop_logic),
        ("Ternary(c, t, f)", prop_ternary),
        ("e==FuncExpr(f==Func(ps, b))", prop_func_expr),
        ("m==Match(p, cs)", prop_match),
        ("e==Attr(s, f)", prop_attr),
        ("e==GetEnv(Env(t))", instantiate_type),
        ("HaveEnv(_)", lambda: C.TPrim(PBool())),
        ("InEnv(Env(t), init, f)", prop_inenv),
        ("MakeCtx(Env(t), init)", prop_makectx),
        ("e==GetExtrinsic(extr, node)", prop_getextrinsic),
        ("e==HasExtrinsic(_, node)", prop_hasextrinsic),
        ("ScopeExtrinsic(_, f)", prop_expr),
        ("bind==Bind(target)", prop_bind))
    if env(GENOPTS).dumpTypes:
        if not matches(e, ('Lit(_) or Bind(Builtin())')):
            print fmtcol('{0}\n  ^Green^gave^N {1}\n', e, rt)
    add_extrinsic(PendingType, e, rt)
    return rt

def consume_value_as(ct, e):
    in_env(EXPRCTXT, e, lambda: unify(_prop_expr(e), ct))

def extract_cdata(t):
    if matches(t, 'CMeta(Subst(TData(_, _)))'):
        t = t.cell.type
    if matches(t, 'TWeak(_)'):
        t = t.refType
    return match(t, ('TData(dt, ts)', tuple2))

def resolve_field_by_name(t, f):
    dt, ts = extract_cdata(t)
    real_field = None
    for ctor in dt.ctors:
        for field in ctor.fields:
            if extrinsic(Name, field) == f:
                assert real_field == None, "Ambiguous field ref %s" % (f,)
                real_field = field
    assert real_field is not None, "%s is not a field in %s" % (f, dt)
    return real_field

def resolve_field_type(t, ft):
    dt, ts = extract_cdata(t)
    tmap = {}
    for tvar, t in ezip(dt.tvars, ts):
        tmap[tvar] = t
    return ctype_replaced(ft, tmap)

def prop_lhs_attr(lhs, s, f):
    t = prop_expr(s)
    # TEMP: resolve the field name now that we have type info
    lhs.attr = resolve_field_by_name(t, f)
    return resolve_field_type(t, lhs.attr.type)

def prop_lhs(lhs):
    t = match(lhs,
        ("LhsVar(v)", prop_local_var),
        ("lhs==LhsAttr(s, f)", prop_lhs_attr))
    add_extrinsic(PendingType, lhs, t)
    return t

def prop_DT(form):
    dtT = vanilla_tdata(form)
    for c in form.ctors:
        set_type(c, ctor_type(c, dtT))

def prop_func_defn(var, f):
    t = extrinsic(TypeOf, var)
    ft = prop_func_expr(var, f, f.params, f.body)
    unify(ft, ctype(t))

def prop_defn(pat, e):
    m = match((pat, e))
    if m("(PatVar(v), FuncExpr(f))"):
        var = m.v
        if has_extrinsic(TypeOf, var):
            cft = ctype(extrinsic(TypeOf, var))
            add_extrinsic(PendingType, e, cft)
            add_extrinsic(PendingType, pat, cft)
            # don't use set_var_ctype since we don't need a pending type
            env(PROPSCOPE).localVars[var] = cft

            prop_func_defn(var, m.f)
            return

    ct = prop_expr(e)
    prop_pat(ct, pat)

def prop_assign(a, e):
    consume_value_as(prop_lhs(a), e)

def prop_augassign(a, e):
    unify(prop_lhs(a), CInt())
    consume_value_as(CInt(), e)

def prop_cond(cases):
    for case in cases:
        consume_value_as(CBool(), case.test)
        prop_body(case.body)

def prop_while(test, body):
    consume_value_as(CBool(), test)
    prop_body(body)

def prop_assert(tst, msg):
    consume_value_as(CBool(), tst)
    consume_value_as(CStr(), msg)

def prop_return(e):
    t = prop_expr(e)
    unify_results(Ret(t), env(PROPSCOPE).result)

def prop_voidreturn():
    assert not matches(env(PROPSCOPE).result, "Ret(_)")

def prop_writeextrinsic(s, extr, node, val):
    prop_expr(node)
    consume_value_as(instantiate_type(s, extr.type), val)

def prop_void_call(call, f, ps):
    result = prop_call_result(call, f, ps)
    assert not matches(result, "Ret(_)"), "%s doesn't return void" % (call,)

def prop_void_inenv(t, init, f):
    consume_value_as(ctype(t), init)
    return prop_voidexpr(f)

def prop_voidexpr(e):
    match(e,
        ("call==VoidCall(f, ps)", prop_void_call),
        ("VoidInEnv(Env(t), init, e)", prop_void_inenv))

def prop_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(pat, e)", prop_defn),
        ("Assign(lhs, e)", prop_assign),
        ("AugAssign(_, lhs, e)", prop_augassign),
        ("Break() or Continue()", nop),
        ("BlockMatch(e, cs)", prop_block_match),
        ("Cond(cases)", prop_cond),
        ("While(t, b)", prop_while),
        ("Assert(t, m)", prop_assert),
        ("Return(e)", prop_return),
        ("ReturnNothing()", prop_voidreturn),
        ("s==WriteExtrinsic(extr, node, val, _)", prop_writeextrinsic),
        ("VoidStmt(e)", prop_voidexpr)))

def prop_body(body):
    map_(prop_stmt, body.stmts)

def site_target_typeof(site):
    if isinstance(site, Expr):
        return extrinsic(TypeOf, site.target)
    elif isinstance(site, Pat):
        return vanilla_tdata(extrinsic(TypeOf, site.ctor).result.type.data)

def prop_top_func(topDefn, topVar, f):

    def go(topVar, f, captures):
        prop_func_defn(topVar, f)
        # Finalize inferred types
        for v, ct in captures[PendingType].iteritems():
            set_type(v, finalize_type(ct))
        # Record instantiations
        sites = captures[PendingInst]

        for site, mapping in sites.iteritems():
            insts = {}
            for tv, ct in mapping.iteritems():
                if matches(ct, "CMeta(InstVar(_))"):
                    continue # Inst w/ old var; no replacement

                instType = finalize_type(ct)

                # check if this replaces the typevar with itself
                # wondering if it's possible to do this check earlier?
                if match(instType, ("TVar(tv2)", lambda tv2: tv is tv2),
                                   ("_", lambda: False)):
                    continue

                insts[tv] = instType
            if len(insts) == 0:
                continue

            # For debugging only (this check is done by the typechecker)
            origT = site_target_typeof(site)
            instT = extrinsic(TypeOf, site)
            assert not type_equal(instT, origT), with_context("Impotent inst",
                    "Type %s unaffected by %s" % (origT, insts))
            if env(GENOPTS).dumpInsts:
                print fmtcol('^Purple^inst ^N{0} ^Purple^w/ types^N {1}',
                        site, insts)
                print '  ', origT
                print mark('->'), instT

            add_extrinsic(Instantiation, site, insts)

    captures = {}
    capture_scoped([PendingType, PendingInst], captures,
        lambda: in_env(PROPTOP, topDefn,
        lambda: go(topVar, f, captures)))

def prop_compilation_unit(unit):
    for f in unit.funcs:
        in_env(STMTCTXT, f, lambda: prop_top_func(f, f.var, f.func))
    vat.visit(EnvInference, unit, t_DT(CompilationUnit))

def prop_top_lit(lit):
    add_extrinsic(TypeOf, lit.var, finalize_type(prop_lit(lit.literal)))

def prop_module_decls(decls):
    map_(prop_DT, decls.dts)
    map_(prop_top_lit, decls.lits)

FuncEnvInfo = DT('FuncEnvInfo', ('envsNeeded', set(['*Env'])),
                                ('conditionalEnvs', set(['*Env'])),
                                ('envsProvided', set(['*Env'])))
FUNCENVS = new_env('FUNCENVS', set(['*Env']))

def infer_func_envs(f, var, visitFunc):
    info = FuncEnvInfo(set(), set(), set())
    in_env(FUNCENVS, info, visitFunc)
    extrinsic(TypeOf, var).meta.requiredEnvs = list(info.envsNeeded)

class EnvInference(vat.Visitor):
    def TopFunc(self, top):
        infer_func_envs(top.func, top.var, lambda: self.visit('func'))

    def FuncExpr(self, fe):
        infer_func_envs(fe.func, fe, lambda: self.visit('func'))

    def GetEnv(self, e):
        scope = env(FUNCENVS)
        if e.env in scope.envsProvided:
            return # provided by an outer in_env()
        if e.env in scope.conditionalEnvs:
            return # preceeded by have_env() (very crude, no flow awareness)
        scope.envsNeeded.add(e.env)

    def HaveEnv(self, e):
        env(FUNCENVS).conditionalEnvs.add(e.env)

    def InEnv(self, e):
        self.visit('init')
        provided = env(FUNCENVS).envsProvided
        introducing = e.env not in provided
        if introducing:
            provided.add(e.env)
        self.visit('expr')
        if introducing:
            provided.remove(e.env)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
