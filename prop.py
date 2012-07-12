#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from globs import TypeOf

TypeCast = new_extrinsic('TypeCast', (Type, Type))

CHECK = new_env('CHECK', '*Type')

UNIFYCTXT = new_env('UNIFYCTXT', '(*Type, *Type)')

PropScope = DT('PropScope', ('retType', 'Maybe(CType)'),
                            ('localVars', {'*Var': 'CType'}))

PROPSCOPE = new_env('PROPSCOPE', 'PropScope')

PropTop = DT('PropTop', ('top', '*TopLevel'),
                        ('deferredExprTypes', {'*Expr': 'CType'}),
                        ('deferredFuncTypes', {'*Func': 'CType'}),
                        ('deferredVarTypes', {'*Var': 'CType'}))

PROPTOP = new_env('PROPTOP', 'PropTop')

MetaVar = new_extrinsic('MetaVar', {'*TypeVar': 'CType'})

def with_context(desc, msg):
    if have_env(UNIFYCTXT):
        src, dest = env(UNIFYCTXT)
        desc = fmtcol("^DG^Types:^N {0} ^DG==>^N {1}\n{2}", src, dest, desc)
    if have_env(EXPRCTXT):
        desc = fmtcol("^DG^Expr:^N {0}\n{1}", env(EXPRCTXT), desc)
    desc = fmtcol("\n^DG^At:^N {0}\n{1}", env(STMTCTXT), desc)
    return fmtcol("^DG{0}^N\n^Red{1}^N", desc, msg)

def in_new_scope(retT, f):
    localVars = {}
    if have_env(PROPSCOPE):
        localVars = env(PROPSCOPE).localVars.copy()
    new_scope = PropScope(retT, localVars)
    return in_env(PROPSCOPE, new_scope, f)

MetaCell = DT('MetaCell', ('type', 'Maybe(CType)'))

# instantiated types
CType, CVar, CPrim, CVoid, CTuple, CFunc, CData, CArray, CWeak, CMeta \
    = ADT('CType',
        'CVar', ('typeVar', '*TypeVar'),
        'CPrim', ('primType', '*PrimType'),
        'CVoid',
        'CTuple', ('tupleTypes', ['CType']),
        'CFunc', ('funcArgs', ['CType']), ('funcRet', 'CType'),
        'CData', ('data', '*DataType'), ('appTypes', ['CType']),
        'CArray', ('elemType', 'CType'),
        'CWeak', ('refType', 'CType'),
        'CMeta', ('cell', MetaCell))

def CInt(): return CPrim(PInt())
def CBool(): return CPrim(PBool())
def CStr(): return CPrim(PStr())

# instantiation lookup for this site
INST = new_env('INST', {TypeVar: Type})
# direct transformation to C* (hacky reuse of _inst_type)
SUBST = new_env('SUBST', {'*TypeVar': Type})

def fresh():
    return CMeta(MetaCell(Nothing()))

def inst_tvar(tv):
    if have_env(SUBST):
        return env(SUBST).get(tv, CVar(tv))
    t = env(INST).get(tv)
    if t is not None:
        return ctype(t)
    else:
        if not has_extrinsic(MetaVar, tv):
            add_extrinsic(MetaVar, tv, fresh())
        return extrinsic(MetaVar, tv)

def inst_tdata(dt, ts):
    insts = []
    for i, tvar in enumerate(dt.tvars):
        insts.append(_inst_type(ts[i]) if i < len(ts) else CVar(tvar))
    return CData(dt, insts)

def _inst_type(s):
    return match(s,
        ('TVar(tv)', inst_tvar),
        ('TPrim(p)', CPrim),
        ('TVoid()', CVoid),
        ('TTuple(ts)', lambda ts: CTuple(map(_inst_type, ts))),
        ('TFunc(ps, r)', lambda ps, r:
                CFunc(map(_inst_type, ps), _inst_type(r))),
        ('TData(dt, ts)', inst_tdata),
        ('TArray(t)', lambda t: CArray(_inst_type(t))),
        ('TWeak(t)', lambda t: CWeak(_inst_type(t))))

def instantiate_type(site, t):
    inst = extrinsic(InstMap, site) if has_extrinsic(InstMap, site) else {}
    return scope_extrinsic(MetaVar, lambda:
            in_env(INST, inst, lambda: _inst_type(t)))

def instantiate(site, v):
    t = extrinsic(TypeOf, v)
    return instantiate_type(site, t)

def ctype(t):
    return in_env(SUBST, {}, lambda: _inst_type(t))

def ctype_replaced(t, substs):
    return in_env(SUBST, substs, lambda: _inst_type(t))

def gen_tdata(dt, ats):
    assert len(ats) == len(dt.tvars)
    return TData(dt, [generalize_type(at) for at in ats])

def gen_new_tvar(cell):
    # XXX need to look for existing annot tvar and use it instead if present
    top = env(PROPTOP).top
    tvar = TypeVar()
    cell.type = Just(CVar(tvar))
    if not has_extrinsic(TypeVars, top):
        add_extrinsic(TypeVars, top, [])
    extrinsic(TypeVars, top).append(tvar)

def _gen_type(s):
    return match(s,
        ('CVar(tv)', TVar),
        ('CPrim(p)', TPrim),
        ('CVoid()', TVoid),
        ('CTuple(ts)', lambda ts: TTuple(map(_gen_type, ts))),
        ('CFunc(ps, r)', lambda ps, r:
                TFunc(map(_gen_type, ps), _gen_type(r))),
        ('CData(dt, ts)', gen_tdata),
        ('CArray(t)', lambda t: TArray(_gen_type(t))),
        ('CWeak(t)', lambda t: TWeak(_gen_type(t))),
        ('CMeta(cell==MetaCell(Nothing()))', gen_new_tvar),
        ('CMeta(MetaCell(Just(s)))', _gen_type))

def generalize_type(t):
    return _gen_type(t)

def unification_failure(src, dest, msg):
    desc = fmtcol("^DG^Couldn't unify^N {0} {1!r}\n^DG^with^N {2} {3!r}",
            type(src), src, type(dest), dest)
    assert False, with_context(desc, msg)

def try_unite_two_metas(src, scell, dest, dcell):
    if scell is dcell:
        pass
    elif isJust(scell.type) and isJust(dcell.type):
        try_unite(fromJust(scell.type), fromJust(dcell.type))
    elif isJust(scell.type):
        # XXX ought to narrow properly
        dest.cell = scell
    else:
        src.cell = dcell

def try_unite_meta(m, mcell, dest):
    if isJust(mcell.type):
        try_unite(fromJust(mcell.type), dest)
    else:
        # zonking dest might be a good idea
        mcell.type = Just(dest)

def try_unite_meta_backwards(dest, m, mcell):
    # XXX ought to narrow properly
    try_unite_meta(m, mcell, dest)

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

def unify(src, dest):
    in_env(UNIFYCTXT, (src, dest), lambda: try_unite(src, dest))

def try_unite(src, dest):
    fail = lambda m: unification_failure(src, dest, m)
    match((src, dest),
        ("(src==CMeta(scell), dest==CMeta(dcell))", try_unite_two_metas),
        ("(m==CMeta(mcell), dest)", try_unite_meta),
        ("(dest, m==CMeta(mcell))", try_unite_meta_backwards),
        ("(src==CVar(stv), dest==CVar(dtv))", try_unite_typevars),
        ("(src==CTuple(t1), dest==CTuple(t2))", try_unite_tuples),
        ("(CArray(t1), CArray(t2))", try_unite),
        ("(sf==CFunc(sa, sr), df==CFunc(da, dr))", try_unite_funcs),
        ("(src==CData(a, ats), dest==CData(b, bts))", try_unite_datas),
        ("(src==CPrim(sp), dest==CPrim(dp))", try_unite_prims),
        ("(CVoid(), CVoid())", nop),
        ("_", lambda: fail("type mismatch")))

def unify_m(e):
    unify(env(CHECK), e)

def set_type(e, t):
    assert isinstance(t, Type), "%s is not a type" % (t,)
    add_extrinsic(TypeOf, e, t)

def set_var_ctype(v, ct):
    if have_env(PROPSCOPE):
        env(PROPSCOPE).localVars[v] = ct
        env(PROPTOP).deferredVarTypes[v] = ct
    else:
        set_type(v, generalize_type(ct))

def set_expr_ctype(e, ct):
    env(PROPTOP).deferredExprTypes[e] = ct

def pat_tuple(ps):
    ts = match(env(CHECK), "CTuple(ps)")
    for p, t in ezip(ps, ts):
        in_env(CHECK, t, lambda: prop_pat(p))

def pat_var(v):
    set_var_ctype(v, env(CHECK))

def pat_capture(v, p):
    pat_var(v)
    prop_pat(p)

def pat_ctor(ref, ctor, args):
    ctorT = instantiate(ref, ctor)
    fieldTs, dt = match(ctorT, ("CFunc(fs, dt)", tuple2))
    unify_m(dt)
    for arg, fieldT in ezip(args, fieldTs):
        in_env(CHECK, fieldT, lambda: prop_pat(arg))

def prop_pat(p):
    # bad type, meh
    return in_env(EXPRCTXT, p, lambda: _prop_pat(p))

def _prop_pat(p):
    match(p,
        ("PatInt(_)", lambda: unify_m(CInt())),
        ("PatStr(_)", lambda: unify_m(CStr())),
        ("PatWild()", nop),
        ("PatTuple(ps)", pat_tuple),
        ("PatVar(v)", pat_var),
        ("PatCapture(v, p)", pat_capture),
        ("p==PatCtor(c, args)", pat_ctor))

def prop_binding_var(b, v):
    ct = env(PROPSCOPE).localVars.get(v)
    if ct is not None:
        return ct
    return instantiate(b, v)

def prop_binding(ref, binding):
    return match(binding,
        ("s==BindVar(v)", prop_binding_var),
        ("s==BindCtor(v)", instantiate),
        ("s==BindBuiltin(v)", instantiate)
    )

def prop_call(f, s):
    ft = prop_expr(f)
    argts = map(prop_expr, s)
    for arg, param in ezip(argts, ft.funcArgs):
        unify(arg, param)
    return ft.funcRet

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
    rt = fresh()
    def inside_func():
        localVars = env(PROPSCOPE).localVars
        pts = []
        for p in ps:
            assert p not in localVars
            pt = fresh()
            set_var_ctype(p, pt)
            pts.append(pt)

        cft = CFunc(pts, rt)
        # lambdas can't recurse, but this (sort of thing) would be nice
        #localVars[f] = cft
        prop_body(b)

        env(PROPTOP).deferredFuncTypes[f] = cft
        return cft
    return in_new_scope(Just(rt), inside_func)

def prop_func(f, ps, b):
    if not has_extrinsic(TypeOf, f):
        return infer_func(f, ps, b)
    ft = extrinsic(TypeOf, f)
    cft = ctype(ft)
    tps, tret = match(cft, ('CFunc(ps, ret)', tuple2))
    def inside_func_scope():
        for p, ctp in ezip(ps, tps):
            set_var_ctype(p, ctp)
        prop_body(b)
        return cft
    return in_new_scope(Just(tret), inside_func_scope)

def prop_match(m, e, cs):
    et = prop_expr(e)
    retT = Nothing()
    for c in cs:
        cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))
        def prop_case():
            in_env(CHECK, et, lambda: prop_pat(cp))
            rt = prop_expr(ce)
            retT = env(PROPSCOPE).retType
            if isJust(retT):
                unify(rt, fromJust(retT))
            else:
                retT = Just(rt)
            return retT
        retT = in_new_scope(retT, prop_case)
    return fromJust(retT)

def prop_attr(e, s, f):
    t = prop_expr(s)
    # TEMP: resolve the field name now that we have type info
    e.field = resolve_field_by_name(t, f)
    return resolve_field_type(t, e.field.type)

def prop_inenv(t, init, f):
    consume_value_as(ctype(t), init)
    return prop_expr(f)

def prop_getextrinsic(e, extr, node):
    t = prop_expr(node)
    assert matches(t, "CData(_, _)"), "Can't get extr from %s" % (nodet,)
    return instantiate_type(e, extr.type)

def prop_hasextrinsic(e, node):
    t = prop_expr(node)
    assert matches(t, "CData(_, _)"), "Can't check for extr from %s" % (nodet,)
    return CBool()

def prop_expr(e):
    return in_env(EXPRCTXT, e, lambda: _prop_expr(e))

def _prop_expr(e):
    rt = match(e,
        ("IntLit(_)", CInt),
        ("StrLit(_)", CStr),
        ("TupleLit(ts)", lambda ts: CTuple(map(prop_expr, ts))),
        ("ListLit(ss)", lambda ts: CList(map(prop_expr, ts))),
        ("Call(f, s)", prop_call),
        ("And(l, r) or Or(l, r)", prop_logic),
        ("Ternary(c, t, f)", prop_ternary),
        ("FuncExpr(f==Func(ps, b))", prop_func),
        ("m==Match(p, cs)", prop_match),
        ("e==Attr(s, f)", prop_attr),
        ("e==GetEnv(Env(t))", instantiate_type),
        ("HaveEnv(_)", lambda: CPrim(PBool())),
        ("InEnv(Env(t), init, f)", prop_inenv),
        ("e==GetExtrinsic(extr, node)", prop_getextrinsic),
        ("e==HasExtrinsic(_, node)", prop_hasextrinsic),
        ("ScopeExtrinsic(_, f)", prop_expr),
        ("ref==Bind(b)", prop_binding))
    if env(GENOPTS).dumpTypes:
        if not matches(e, ('IntLit(_) or StrLit(_) or Bind(BindBuiltin(_))')):
            print fmtcol('{0}\n  ^Green^gave^N {1}\n', e, rt)
    set_expr_ctype(e, rt)
    return rt

def consume_value_as(ct, e):
    in_env(EXPRCTXT, e, lambda: unify(_prop_expr(e), ct))

def resolve_field_by_name(t, f):
    dt = match(t, "CData(t, _)")
    real_field = None
    for ctor in dt.ctors:
        for field in ctor.fields:
            if extrinsic(Name, field) == f:
                assert real_field == None, "Ambiguous field ref %s" % (f,)
                real_field = field
    assert real_field is not None, "%s is not a field in %s" % (f, dt)
    return real_field

def resolve_field_type(t, ft):
    dt, ts = match(t, ('CData(dt, ts)', tuple2))
    tmap = {}
    for tvar, t in ezip(dt.tvars, ts):
        tmap[tvar] = t
    return ctype_replaced(ft, tmap)

def prop_lhs_var(lhs, v):
    return prop_binding_var(lhs, v)

def prop_lhs_attr(lhs, s, f):
    t = prop_expr(s)
    # TEMP: resolve the field name now that we have type info
    lhs.attr = resolve_field_by_name(t, f)
    return resolve_field_type(t, lhs.attr.type)

def prop_lhs(lhs):
    return match(lhs,
        ("LhsVar(v)", lambda v: env(PROPSCOPE).localVars[v]),
        ("lhs==LhsAttr(s, f)", prop_lhs_attr))

def prop_DT(form):
    dtT = TData(form, [])
    for c in form.ctors:
        set_type(c, TFunc([f.type for f in c.fields], dtT))

def destructure_tuple(ps, t):
    ts = match(t, "CTuple(ts)")
    for p, t in ezip(ps, ts):
        destructure_pat(p, t)

def destructure_pat(pat, t):
    match(pat, ("PatVar(v)", lambda v: set_var_ctype(v, t)),
               ("PatTuple(ps)", lambda ps: destructure_tuple(ps, t)))

def prop_defn(pat, e):
    m = match(e)
    if m("FuncExpr(f)"):
        f = m.arg
        if has_extrinsic(TypeOf, f):
            t = extrinsic(TypeOf, f)
            v = match(pat, "PatVar(v)")
            set_type(v, t)
            consume_value_as(ctype(t), e)
            return

    ct = prop_expr(e)
    destructure_pat(pat, ct)

def prop_assign(a, e):
    consume_value_as(prop_lhs(a), e)

def prop_augassign(a, e):
    unify(prop_lhs(a), CInt())
    consume_value_as(CInt(), e)

def prop_cond(cases, else_):
    for case in cases:
        consume_value_as(CBool(), case.test)
        prop_body(case.body)
    if isJust(else_):
        prop_body(fromJust(else_))

def prop_while(test, body):
    consume_value_as(CBool(), test)
    prop_body(body)

def prop_assert(tst, msg):
    consume_value_as(CBool(), tst)
    consume_value_as(CStr(), msg)

def prop_return(e):
    unify(prop_expr(e), env(PROPSCOPE).retType.just)

def prop_returnnothing():
    assert isNothing(env(PROPSCOPE).retType), "Returned nothing"

def prop_writeextrinsic(s, extr, node, val):
    nodet = prop_expr(node)
    assert matches(nodet, "CData(_, _)"), "Can't add extr to %s" % (nodet,)
    consume_value_as(instantiate_type(s, extr.type), val)

def prop_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(pat, e)", prop_defn),
        ("Assign(lhs, e)", prop_assign),
        ("AugAssign(_, lhs, e)", prop_augassign),
        ("Break() or Continue()", nop),
        ("ExprStmt(e)", prop_expr),
        ("Cond(cases, elseCase)", prop_cond),
        ("While(t, b)",prop_while),
        ("Assert(t, m)", prop_assert),
        ("Return(e)", prop_return),
        ("ReturnNothing()", prop_returnnothing),
        ("s==WriteExtrinsic(extr, node, val, _)", prop_writeextrinsic)))

def prop_body(body):
    for s in body.stmts:
        prop_stmt(s)

def prop_top_defn(topDefn, pat, e):
    top = PropTop(topDefn, {}, {}, {})
    def go(pat, e):
        prop_defn(pat, e)
        for v, ct in top.deferredVarTypes.iteritems():
            set_type(v, generalize_type(ct))
        for e, ct in top.deferredExprTypes.iteritems():
            set_type(e, generalize_type(ct))
        for f, ct in top.deferredFuncTypes.iteritems():
            set_type(f, generalize_type(ct))
    in_env(PROPTOP, top, lambda: go(pat, e))

def prop_top_level(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("TopCDecl(_)", nop),
        ("TopDT(form)", prop_DT),
        ("TopEnv(_)", nop),
        ("top==TopDefn(pat, e)", prop_top_defn),
        ("TopExtrinsic(_)", nop)))

def prop_compilation_unit(unit):
    map_(prop_top_level, unit.tops)

def prop_types(root):
    captures = {}
    annots = {}
    capture_scoped([TypeCast], captures,
        lambda: capture_extrinsic(TypeOf, annots,
        lambda: prop_compilation_unit(root)
    ))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
