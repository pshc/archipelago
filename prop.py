#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from globs import TypeOf

INPAT = new_env('INPAT', '*Type')

PropScope = DT('PropScope', ('retType', 'Maybe(CType)'),
                            ('localVars', {'*Var': 'CType'}))

PROPSCOPE = new_env('PROPSCOPE', 'PropScope')

PROPTOP = new_env('PROPTOP', '*TopFunc')

InstSite = new_extrinsic('InstSite', {'*TypeVar': 'CType'})

def in_new_scope(retT, f):
    localVars = {}
    if have_env(PROPSCOPE):
        localVars = env(PROPSCOPE).localVars.copy()
    new_scope = PropScope(retT, localVars)
    return in_env(PROPSCOPE, new_scope, f)

MetaCell, Free, InstVar, Mono, Subst = ADT('MetaCell',
    'Free', ('typeVar', 'Maybe(TypeVar)'),
    'InstVar', ('origTypeVar', '*TypeVar'),
    'Mono',
    'Subst', ('type', 'CType'))

# instantiated types
CType, CVar, CPrim, CVoid, CTuple, CFunc, CData, CArray, CWeak, CMeta \
    = ADT('CType',
        'CVar', ('typeVar', '*TypeVar'),
        'CPrim', ('primType', '*PrimType'),
        'CVoid',
        'CTuple', ('tupleTypes', ['CType']),
        'CFunc', ('paramTypes', ['CType']), ('retType', 'CType'),
        'CData', ('data', '*DataType'), ('appTypes', ['CType']),
        'CArray', ('elemType', 'CType'),
        'CWeak', ('refType', 'CType'),
        'CMeta', ('cell', MetaCell))

PendingType = new_extrinsic('PendingType', CType)

def CInt(): return CPrim(PInt())
def CFloat(): return CPrim(PFloat())
def CBool(): return CPrim(PBool())
def CStr(): return CPrim(PStr())

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
        return env(SUBST).get(tv, CVar(tv))
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
    return CData(dt, map(_inst_type, ts))

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
    insts = {}
    hints = extrinsic(InstMap, site) if has_extrinsic(InstMap, site) else {}
    ct = in_env(INST, InstInfo(insts, hints), lambda: _inst_type(t))
    if len(insts) > 0:
        add_extrinsic(InstSite, site, insts)
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
        ('CVar(tv)', TVar),
        ('CPrim(p)', TPrim),
        ('CVoid()', TVoid),
        ('CTuple(ts)', lambda ts: TTuple(map(_gen_type, ts))),
        ('CFunc(ps, r)', lambda ps, r:
                TFunc(map(_gen_type, ps), _gen_type(r))),
        ('CData(dt, ts)', gen_tdata),
        ('CArray(t)', lambda t: TArray(_gen_type(t))),
        ('CWeak(t)', lambda t: TWeak(_gen_type(t))),
        ('CMeta(Free(Just(tvar)))', TVar),
        ('CMeta(f==Free(Nothing()))', capture_free),
        ('CMeta(InstVar(tv))', TVar),
        ('CMeta(Mono())', free_monotype),
        ('CMeta(Subst(s))', _gen_type))

def finalize_type(t):
    return _gen_type(t)

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
    match((src, dest),
        ("(CMeta(Subst(s)), CMeta(Subst(d)))", try_unite),
        # two free vars
        ("(src==CMeta(Free(_)), t==CMeta(Free(_) or InstVar(_) or Mono()))",
                set_meta_subst),
        ("(src==CMeta(InstVar(_)), t==CMeta(Free(_) or InstVar(_) or Mono()))",
                set_meta_subst),
        ("(src==CMeta(Mono()), t==CMeta(Mono()))", set_meta_subst),
        ("(src==CMeta(Mono()), t==CMeta(Free(_) or InstVar(_)))",
                copy_mono_subst),
        # free -> some type (direct unification)
        ("(CMeta(Subst(src)), dest)", try_unite),
        ("(CMeta(Mono()), CVar(_))", lambda:
            fail("Can't infer polytype for func params/ret; provide annot")),
        ("(m==CMeta(_), dest)", set_meta_subst),
        # some type -> free (possible generalization)
        ("(dest, m==CMeta(_))", try_unite_meta_backwards),

        ("(src==CVar(stv), dest==CVar(dtv))", try_unite_typevars),
        ("(src==CTuple(t1), dest==CTuple(t2))", try_unite_tuples),
        ("(CArray(t1), CArray(t2))", try_unite),
        ("(sf==CFunc(sa, sr), df==CFunc(da, dr))", try_unite_funcs),
        ("(src==CData(a, ats), dest==CData(b, bts))", try_unite_datas),
        ("(src==CPrim(sp), dest==CPrim(dp))", try_unite_prims),
        ("(CVoid(), CVoid())", nop),
        ("_", lambda: fail("type mismatch")))

def unify(src, dest):
    in_env(UNIFYCTXT, (src, dest), lambda: try_unite(src, dest))

def unify_m(e):
    unify(env(INPAT), e)

def set_type(e, t):
    assert isinstance(t, Type), "%s is not a type" % (t,)
    add_extrinsic(TypeOf, e, t)

def set_var_ctype(v, ct):
    if have_env(PROPSCOPE):
        env(PROPSCOPE).localVars[v] = ct
    add_extrinsic(PendingType, v, ct)

def pat_tuple(ps):
    ts = match(env(INPAT), "CTuple(ps)")
    for p, t in ezip(ps, ts):
        in_env(INPAT, t, lambda: _prop_pat(p))

def pat_var(v):
    set_var_ctype(v, env(INPAT))

def pat_capture(v, p):
    pat_var(v)
    _prop_pat(p)

def pat_ctor(ref, ctor, args):
    ctorT = instantiate_type(ref, extrinsic(TypeOf, ctor))
    fieldTs, dt = match(ctorT, ("CFunc(fs, dt)", tuple2))
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

def inst_bind(bind, v):
    t = extrinsic(TypeOf, v)
    return instantiate_type(bind, extrinsic(TypeOf, v))

def prop_bind(b, target):
    v = Bindable.isVar(target)
    if isJust(v):
        return prop_bind_var(b, fromJust(v))
    else:
        return inst_bind(b, target)

def prop_bind_var(b, v):
    ct = env(PROPSCOPE).localVars.get(v)
    if ct is not None:
        return ct
    return inst_bind(b, v)

def prop_lit(lit):
    return ctype(lit_type(lit))

def prop_listlit(es):
    if len(es) == 0:
        return CArray(fresh())
    else:
        t = prop_expr(es[0])
        for e in es[1:]:
            consume_value_as(t, e)
        return CArray(t)

def prop_call(call, f, s):
    ft = prop_expr(f)
    argts = map(prop_expr, s)

    # TEMP: resolve numeric operator overload
    if 1 <= len(argts) <= 2 and matches(argts[0], "CPrim(PFloat())") and \
                matches(f, "Bind(_)"):
        newf = overload_num_call(f.target)
        if newf:
            f = newf
            call.func = f
            ft = prop_expr(f)

    for arg, param in ezip(argts, ft.paramTypes):
        unify(arg, param)
    return ft.retType

def overload_num_call(f):
    if matches(f, "key('negate')"):
        return builtin_ref('fnegate')

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
    rt = fresh_monotype()
    def inside_func():
        localVars = env(PROPSCOPE).localVars
        pts = []
        for p in ps:
            assert p not in localVars
            pt = fresh_monotype()
            set_var_ctype(p, pt)
            pts.append(pt)

        cft = CFunc(pts, rt)
        # lambdas can't recurse, but this (sort of thing) would be nice
        #localVars[f] = cft
        prop_body(b)

        add_extrinsic(PendingType, f, cft)
        return cft
    return in_new_scope(Just(rt), inside_func)

def prop_func_expr(f, ps, b):
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
            prop_pat(et, cp)
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
        ("Lit(lit)", prop_lit),
        ("TupleLit(ts)", lambda ts: CTuple(map(prop_expr, ts))),
        ("ListLit(ss)", prop_listlit),
        ("call==Call(f, s)", prop_call),
        ("And(l, r) or Or(l, r)", prop_logic),
        ("Ternary(c, t, f)", prop_ternary),
        ("FuncExpr(f==Func(ps, b))", prop_func_expr),
        ("m==Match(p, cs)", prop_match),
        ("e==Attr(s, f)", prop_attr),
        ("e==GetEnv(Env(t))", instantiate_type),
        ("HaveEnv(_)", lambda: CPrim(PBool())),
        ("InEnv(Env(t), init, f)", prop_inenv),
        ("e==GetExtrinsic(extr, node)", prop_getextrinsic),
        ("e==HasExtrinsic(_, node)", prop_hasextrinsic),
        ("ScopeExtrinsic(_, f)", prop_expr),
        ("bind==Bind(target)", prop_bind))
    if env(GENOPTS).dumpTypes:
        if not matches(e, ('Lit(_) or Bind(BindBuiltin(_))')):
            print fmtcol('{0}\n  ^Green^gave^N {1}\n', e, rt)
    add_extrinsic(PendingType, e, rt)
    return rt

def consume_value_as(ct, e):
    in_env(EXPRCTXT, e, lambda: unify(_prop_expr(e), ct))

def extract_cdata(t):
    return match(t, ('CData(dt, ts) or CMeta(Subst(CData(dt, ts)))', tuple2))

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

def prop_lhs_var(lhs, v):
    return prop_bind_var(lhs, v)

def prop_lhs_attr(lhs, s, f):
    t = prop_expr(s)
    # TEMP: resolve the field name now that we have type info
    lhs.attr = resolve_field_by_name(t, f)
    return resolve_field_type(t, lhs.attr.type)

def prop_lhs(lhs):
    t = match(lhs,
        ("LhsVar(v)", lambda v: env(PROPSCOPE).localVars[v]),
        ("lhs==LhsAttr(s, f)", prop_lhs_attr))
    add_extrinsic(PendingType, lhs, t)
    return t

def prop_DT(form):
    dtT = vanilla_tdata(form)
    for c in form.ctors:
        set_type(c, TFunc([f.type for f in c.fields], dtT))

def prop_func_defn(var, f):
    t = extrinsic(TypeOf, f)
    set_type(var, t)
    ft = prop_func_expr(f, f.params, f.body)
    unify(ft, ctype(t))

def prop_defn(pat, e):
    m = match(e)
    if m("FuncExpr(f)"):
        f = m.arg
        if has_extrinsic(TypeOf, f):
            t = extrinsic(TypeOf, f)
            prop_func_defn(match(pat, "PatVar(v)"), f)
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
    unify(prop_expr(e), env(PROPSCOPE).retType.just)

def prop_writeextrinsic(s, extr, node, val):
    prop_expr(node)
    consume_value_as(instantiate_type(s, extr.type), val)

def prop_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(pat, e)", prop_defn),
        ("Assign(lhs, e)", prop_assign),
        ("AugAssign(_, lhs, e)", prop_augassign),
        ("Break() or Continue()", nop),
        ("ExprStmt(e)", prop_expr),
        ("Cond(cases)", prop_cond),
        ("While(t, b)",prop_while),
        ("Assert(t, m)", prop_assert),
        ("Return(e)", prop_return),
        ("ReturnNothing()", nop),
        ("s==WriteExtrinsic(extr, node, val, _)", prop_writeextrinsic)))

def prop_body(body):
    for s in body.stmts:
        prop_stmt(s)

def site_target_typeof(site):
    if isinstance(site, Expr):
        return extrinsic(TypeOf, site.target)
    elif isinstance(site, Pat):
        return vanilla_tdata(extrinsic(TypeOf, site.ctor).retType.data)

def prop_top_func(topDefn, topVar, f):

    def go(topVar, f, captures):
        prop_func_defn(topVar, f)
        # Finalize inferred types
        for v, ct in captures[PendingType].iteritems():
            set_type(v, finalize_type(ct))
        # Record instantiations
        sites = captures[InstSite]

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
    capture_scoped([PendingType, InstSite], captures,
        lambda: in_env(PROPTOP, topDefn,
        lambda: go(topVar, f, captures)))

def prop_compilation_unit(unit):
    for f in unit.funcs:
        in_env(STMTCTXT, f, lambda: prop_top_func(f, f.var, f.func))

def prop_top_lit(lit):
    add_extrinsic(TypeOf, lit.var, finalize_type(prop_lit(lit.literal)))

def prop_module_decls(decls):
    map_(prop_DT, decls.dts)
    map_(prop_top_lit, decls.lits)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
