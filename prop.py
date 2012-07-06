#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from globs import TypeOf

TypeCast = new_extrinsic('TypeCast', (Type, Type))
FieldDT = new_extrinsic('FieldDT', '*DataType')

CHECK = new_env('CHECK', '*Type')

UNIFYCTXT = new_env('UNIFYCTXT', '(*Type, *Type)')

PropScope = DT('PropScope', ('level', int),
                            ('retType', 'Maybe(Type)'),
                            ('closedVars', {str: TypeVar}))

PROPSCOPE = new_env('PROPSCOPE', 'PropScope')

def with_context(desc, msg):
    if have_env(UNIFYCTXT):
        src, dest = env(UNIFYCTXT)
        desc = fmtcol("^DG^Types:^N {0} ^DG==>^N {1}\n{2}", src, dest, desc)
    if have_env(EXPRCTXT):
        desc = fmtcol("^DG^Expr:^N {0}\n{1}", env(EXPRCTXT), desc)
    desc = fmtcol("\n^DG^At:^N {0}\n{1}", env(STMTCTXT), desc)
    return fmtcol("^DG{0}^N\n^Red{1}^N", desc, msg)

def global_scope():
    return PropScope(0, Nothing(), {})

def in_new_scope(retT, f):
    last = env(PROPSCOPE)
    new_scope = PropScope(last.level+1, retT, last.closedVars.copy())
    return in_env(PROPSCOPE, new_scope, f)

# instantiated types
CType, CVar, CPrim, CVoid, CTuple, CFunc, CData, CArray, CWeak \
    = ADT('CType',
        'CVar', ('typeVar', '*TypeVar'),
        'CPrim', ('primType', '*PrimType'),
        'CVoid',
        'CTuple', ('tupleTypes', ['CType']),
        'CFunc', ('funcArgs', ['CType']), ('funcRet', 'CType'),
        'CData', ('data', '*DataType'), ('appTypes', ['CType']),
        'CArray', ('elemType', 'CType'),
        'CWeak', ('refType', 'CType'))

def CInt(): return CPrim(PInt())
def CBool(): return CPrim(PBool())
def CStr(): return CPrim(PStr())

# instantiation lookup for this site
INST = new_env('INST', {TypeVar: Type})
# direct transformation to C* (hacky reuse of _inst_type)
SUBST = new_env('SUBST', {'*TypeVar': Type})

def instantiate_tvar(tv):
    if have_env(SUBST):
        return env(SUBST).get(tv, CVar(tv))
    t = env(INST).get(tv)
    if t is not None:
        return ctype(t)
    else:
        return CVar(tv) # free

def instantiate_tdata(dt, ts):
    insts = []
    for i, tvar in enumerate(dt.tvars):
        insts.append(_inst_type(ts[i]) if i < len(ts) else CVar(tvar))
    return CData(dt, insts)

def _inst_type(s):
    return match(s,
        ('TVar(tv)', instantiate_tvar),
        ('TPrim(p)', CPrim),
        ('TVoid()', CVoid),
        ('TTuple(ts)', lambda ts: CTuple(map(_inst_type, ts))),
        ('TFunc(ps, r)', lambda ps, r:
                CFunc(map(_inst_type, ps), _inst_type(r))),
        ('TData(dt, ts)', instantiate_tdata),
        ('TArray(t)', lambda t: CArray(_inst_type(t))),
        ('TWeak(t)', lambda t: CWeak(_inst_type(t))))

def instantiate_type(site, t):
    inst = extrinsic(InstMap, site) if has_extrinsic(InstMap, site) else {}
    return in_env(INST, inst, lambda: _inst_type(t))

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
        ('CWeak(t)', lambda t: TWeak(_gen_type(t))))

def generalize_type(t):
    return _gen_type(t)

def unification_failure(src, dest, msg):
    desc = fmtcol("^DG^Couldn't unify^N {0} {1!r}\n^DG^with^N {2} {3!r}",
            type(src), src, type(dest), dest)
    assert False, with_context(desc, msg)

def try_unite_tuples(src, list1, dest, list2):
    if len(list1) != len(list2):
        unification_failure(src, dest, "length mismatch")
    for s, d in zip(list1, list2):
        try_unite(s, d)

def try_unite_funcs(sf, sargs, sret, df, dargs, dret):
    try_unite_tuples(sf, sargs, df, dargs)
    try_unite(sret, dret)

def try_unite_datas(src, a, ats, dest, b, bts):
    if a is not b:
        unification_failure(src, dest, "mismatched datatypes")
    assert len(ats) == len(a.tvars), "Wrong %s typevar count" % (a,)
    assert len(ats) == len(bts), "%s typevar count mismatch" % (a,)
    for at, bt in zip(ats, bts):
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

def pat_tuple(ps):
    ts = match(env(CHECK), ("CTuple(ps)", identity))
    assert len(ps) == len(ts), "Tuple pattern length mismatch"
    for p, t in zip(ps, ts):
        in_env(CHECK, t, lambda: prop_pat(p))

def pat_var(v):
    set_type(v, generalize_type(env(CHECK)))

def pat_capture(v, p):
    pat_var(v)
    prop_pat(p)

def pat_ctor(ref, ctor, args):
    ctorT = instantiate(ref, ctor)
    fieldTs, dt = match(ctorT, ("CFunc(fs, dt)", tuple2))
    unify_m(dt)
    assert len(args) == len(fieldTs), "Wrong ctor param count"
    for arg, fieldT in zip(args, fieldTs):
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

def prop_binding(ref, binding):
    return match(binding,
        ("s==BindVar(v)", instantiate),
        ("s==BindCtor(v)", instantiate),
        ("s==BindBuiltin(v)", instantiate)
    )

def prop_call(f, s):
    ft = prop_expr(f)
    argts = map(prop_expr, s)
    assert len(ft.funcArgs) == len(argts), "Arg count mismatch"
    for t1, t2 in zip(ft.funcArgs, argts):
        unify(t1, t2)
    return ft.funcRet

def prop_logic(l, r):
    consume_value_as(TBool(), l)
    consume_value_as(TBool(), r)
    return CBool()

def prop_ternary(c, t, f):
    consume_value_as(TBool(), c)
    tt = prop_expr(t)
    tf = prop_expr(f)
    unify(tt, tf)
    return tf

def prop_func(f, ps, b):
    tvars = {}
    ft = extrinsic(TypeOf, f)
    tps, tret = match(ft, ('TFunc(tps, tret)', tuple2))
    assert len(tps) == len(ps), "Mismatched param count: %s\n%s" % (tps, ps)
    cft = ctype(ft)
    def inside_func_scope():
        closed = env(PROPSCOPE).closedVars
        for tvar in tvars.itervalues():
            closed[extrinsic(Name, tvar)] = tvar
        for p, tp in zip(ps, tps):
            set_type(p, tp)
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
                unify(rt, ctype(fromJust(retT)))
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
    consume_value_as(t, init)
    return prop_expr(f)

def prop_getextrinsic(e, extr, node):
    t = prop_expr(node)
    assert matches(t, "CData(_, _)"), "Can't get extr from %s" % (nodet,)
    return instantiate_type(e, extr.type)

def unknown_prop(a):
    assert False, with_context('Unknown prop case:', a)

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
        ("ScopeExtrinsic(_, f)", prop_expr),
        ("ref==Bind(b)", prop_binding),
        ("otherwise", unknown_prop))
    if env(GENOPTS).dumpTypes:
        if not matches(e, ('IntLit(_) or StrLit(_) or Bind(BindBuiltin(_))')):
            print fmtcol('{0}\n  ^Green^gave^N {1}\n', e, rt)
    set_type(e, generalize_type(rt))
    return rt

def consume_value_as(t, e):
    ct = ctype(t)
    in_env(EXPRCTXT, e, lambda: unify(ct, _prop_expr(e)))

def resolve_field_by_name(t, f):
    dt = match(t, ("CData(t, _)", identity))
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
    assert len(ts) == len(dt.tvars)
    for tvar, t in zip(dt.tvars, ts):
        tmap[tvar] = t
    return ctype_replaced(ft, tmap)

def prop_lhs_attr(lhs, s, f):
    t = prop_expr(s)
    # TEMP: resolve the field name now that we have type info
    lhs.attr = resolve_field_by_name(t, f)
    return generalize_type(resolve_field_type(t, lhs.attr.type))

def prop_lhs_tuple(lhs, ss):
    t = TTuple(map(prop_lhs, ss))
    set_type(lhs, t)
    return t

def prop_lhs(lhs):
    return match(lhs,
        ("LhsVar(v)", lambda v: extrinsic(TypeOf, v)),
        ("lhs==LhsAttr(s, f)", prop_lhs_attr),
        ("lhs==LhsTuple(ss)", prop_lhs_tuple))

def check_lhs(t, lhs):
    unify(t, prop_lhs(lhs))

def prop_DT(form):
    dtT = TData(form, [])
    for c in form.ctors:
        fieldTs = []
        for f in c.fields:
            add_extrinsic(FieldDT, f, form)
            fieldTs.append(f.type)
        set_type(c, TFunc(fieldTs, dtT))

def prop_new_env(environ):
    # TODO
    pass

def prop_new_extrinsic(ext):
    # XXX: Should have a declarative area for this kind of stuff
    #      so I can unify all this lookup business
    pass

def prop_defn(a, e):
    m = match(e)
    if m("FuncExpr(f)"):
        f = m.arg
        t = extrinsic(TypeOf, f)
        set_type(a, t)
        consume_value_as(t, e)
    else:
        set_type(a, generalize_type(prop_expr(e)))

def prop_addextrinsic(extr, node, val):
    nodet = prop_expr(node)
    assert matches(nodet, "CData(_, _)"), "Can't add extr to %s" % (nodet,)
    consume_value_as(extr.type, val)

def prop_assign(a, e):
    consume_value_as(prop_lhs(a), e)

def prop_augassign(a, e):
    unify(ctype(prop_lhs(a)), CInt())
    consume_value_as(TInt(), e)

def prop_cond(cases, else_):
    for case in cases:
        consume_value_as(TBool(), case.test)
        prop_body(case.body)
    if isJust(else_):
        prop_body(fromJust(else_))

def prop_while(test, body):
    consume_value_as(TBool(), test)
    prop_body(body)

def prop_assert(tst, msg):
    consume_value_as(TBool(), tst)
    consume_value_as(TStr(), msg)

def prop_return(e):
    consume_value_as(env(PROPSCOPE).retType.just, e)

def prop_returnnothing():
    assert isNothing(env(PROPSCOPE).retType), "Returned nothing"

def prop_stmt(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("Defn(var, e)", prop_defn),
        ("AddExtrinsic(extr, node, val)", prop_addextrinsic),
        ("Assign(lhs, e)", prop_assign),
        ("AugAssign(_, lhs, e)", prop_augassign),
        ("Break() or Continue()", nop),
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
        ("TopCDecl(_)", nop),
        ("TopDT(form)", prop_DT),
        ("TopEnv(environ)", prop_new_env),
        ("TopDefn(var, e)", prop_defn),
        ("TopExtrinsic(extr)", prop_new_extrinsic),
        ("otherwise", unknown_prop)))

def prop_compilation_unit(unit):
    map_(prop_top_level, unit.tops)

def with_fields(func):
    def go():
        # Ought to just do this globally.
        """
        for dt in DATATYPES.itervalues():
            prop_DT(dt.__form__)
        """
        return func()
    return scope_extrinsic(FieldDT, go)

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
