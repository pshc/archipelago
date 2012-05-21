#!/usr/bin/env python2
from atom import *
from base import *
from types_builtin import *
from ast import AstType, AstHint
from globs import TypeOf

TypeCast = new_extrinsic('TypeCast', (Type, Type))
FieldDT = new_extrinsic('FieldDT', '*DataType')

PROP = new_env('PROP', '*Type')

STMTCTXT = new_env('STMTCTXT', '*Stmt')

PropScope = DT('PropScope', ('level', int),
                            ('retType', 'Maybe(CType)'),
                            ('closedVars', {str: TypeVar}))

PROPSCOPE = new_env('PROPSCOPE', 'PropScope')

def with_context(msg):
    return match(env(STMTCTXT),
        ("Just(s)", lambda s: "At:\n%s\n%s" % (s, msg)),
        ("_", lambda: msg))

def global_scope():
    return PropScope(0, Nothing(), {})

def in_new_scope(retT, f):
    last = env(PROPSCOPE)
    new_scope = PropScope(last.level+1, retT, last.closedVars.copy())
    return in_env(PROPSCOPE, new_scope, f)

# instantiated types
CType, CVar, CPrim, CVoid, CTuple, CAnyTuple, CFunc, CData, CArray, CWeak \
    = ADT('CType',
        'CVar', ('typeVar', '*TypeVar'), ('appType', 'CType'),
        'CPrim', ('primType', '*PrimType'),
        'CVoid',
        'CTuple', ('tupleTypes', ['CType']),
        'CAnyTuple',
        'CFunc', ('funcArgs', ['CType']), ('funcRet', 'CType'),
        'CData', ('data', '*DataType'), ('appTypes', ['CType']),
        'CArray', ('elemType', 'CType'),
        'CWeak', ('refType', 'CType'))

def CInt(): return CPrim(PInt())
def CBool(): return CPrim(PBool())
def CStr(): return CPrim(PStr())

INST = new_env('INST', {Type: Type})

def instantiate_tvar(tv):
    t = env(INST).get(extrinsic(Name, tv)) # XXX
    if t is None:
        t = TVar(tv) # free
    return CVar(tv, t)

def instantiate_tdata(dt):
    return CData(dt, []) # XXX

def _inst_type(s):
    return match(s,
        ('TVar(tv)', instantiate_tvar),
        ('TPrim(p)', CPrim),
        ('TVoid()', CVoid),
        ('TTuple(ts)', lambda ts: CTuple(map(_inst_type, ts))),
        ('TAnyTuple()', CAnyTuple),
        ('TFunc(ps, r)', lambda ps, r:
                CFunc(map(_inst_type, ps), _inst_type(r))),
        ('TData(dt)', instantiate_tdata),
        ('TArray(t)', lambda t: CArray(_inst_type(t))),
        ('TWeak(t)', lambda t: CWeak(_inst_type(t))))

def instantiate_type(t, ref):
    overrides = {}
    if has_extrinsic(AstHint, ref):
        overrides = extrinsic(AstHint, ref)
    return in_env(INST, overrides, lambda: _inst_type(t))

def instantiate(v, ref):
    t = extrinsic(TypeOf, v)
    print t
    return instantiate_type(t, ref)

def _gen_type(s):
    return match(s,
        ('CVar(tv, _)', TVar),
        ('CPrim(p)', TPrim),
        ('CVoid()', TVoid),
        ('CTuple(ts)', lambda ts: TTuple(map(_gen_type, ts))),
        ('CAnyTuple()', TAnyTuple),
        ('CFunc(ps, r)', lambda ps, r:
                TFunc(map(_gen_type, ps), _gen_type(r))),
        ('CData(dt, _)', TData),
        ('CArray(t)', lambda t: TArray(_gen_type(t))),
        ('CWeak(t)', lambda t: TWeak(_gen_type(t))))

def generalize_type(t):
    return _gen_type(t)

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

def unify_prims(p1, p2, e1, e2):
    if not prim_equal(p1, p2):
        unification_failure(e1, e2, "primitive types")

def unify(e1, e2):
    same = nop
    fail = lambda m: unification_failure(e1, e2, m)
    match((e1, e2),
        ("(CVar(_, _), CVar(_, _))", same), # TEMP
        ("(CTuple(t1), CTuple(t2))",
            lambda t1, t2: unify_tuples(e1, t1, e2, t2, "tuple")),
        ("(CArray(t1), CArray(t2))", unify),
        ("(f1==CFunc(a1, r1), f2==CFunc(a2, r2))", unify_funcs),
        ("(CData(a, _), CData(b, _))", lambda a, b: same() if a is b # XXX
                                 else fail("mismatched datatypes")),
        ("(CPrim(p1), CPrim(p2))", lambda p1, p2: unify_prims(p1, p2, e1, e2)),
        ("(CVoid(), CVoid())", same),
        ("(CTuple(_), CAnyTuple())", same),
        ("(CAnyTuple(), CTuple(_))", same),
        ("(CAnyTuple(), _)", lambda: fail("tuple expected")),
        ("(_, CAnyTuple())", lambda: fail("tuple expected")),
        ("_", lambda: fail("type mismatch")))

def unify_m(e):
    unify(env(PROP), e)

def set_type(e, t):
    assert isinstance(t, Type), "%s is not a type" % (t,)
    add_extrinsic(TypeOf, e, t)

def pat_tuple(ps):
    ts = match(env(PROP), ("CTuple(ps)", identity))
    assert len(ps) == len(ts), "Tuple pattern length mismatch"
    for p, t in zip(ps, ts):
        in_env(PROP, t, lambda: prop_pat(p))

def pat_var(v):
    set_type(v, generalize_type(env(PROP)))

def pat_capture(v, p):
    pat_var(v)
    prop_pat(p)

def pat_ctor(ref, ctor, args):
    ctorT = instantiate(get_type(ctor), ref)
    fieldTs, dt = match(ctorT, ("CFunc(fs, dt)", tuple2))
    unify_m(dt)
    assert len(args) == len(fieldTs), "Wrong ctor param count"
    for arg, fieldT in zip(args, fieldTs):
        in_env(PROP, fieldT, lambda: check_pat(arg))

def prop_pat(p):
    match(p,
        ("PatInt(_)", lambda: unify_m(CPrim(PInt()))),
        ("PatStr(_)", lambda: unify_m(CPrim(PStr()))),
        ("PatWild()", lambda: None),
        ("PatTuple(ps)", pat_tuple),
        ("PatVar(v)", pat_var),
        ("PatCapture(v, p)", pat_capture),
        ("p==PatCtor(c, args)", pat_ctor))

def prop_binding(ref, binding):
    return match(binding,
        ("BindVar(v) or BindCtor(v)", lambda v: instantiate(v, ref)),
        ("BindBuiltin(b)", lambda b:
            instantiate_type(extrinsic(TypeOf, b), ref)),
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
    ft = in_env(NEWTYPEVARS, None, lambda:
            in_env(TVARS, tvars, lambda: parse_type(extrinsic(AstType, f))))
    tps, tret = match(ft, ('TFunc(tps, tret)', tuple2))
    assert len(tps) == len(ps), "Mismatched param count: %s\n%s" % (tps, ps)
    set_type(f, ft)
    cft = instantiate_type(ft, f)
    cret = match(cft, ('CFunc(_, cret)', Just))
    def inside_func_scope():
        closed = env(PROPSCOPE).closedVars
        for tvar in tvars.itervalues():
            closed[extrinsic(Name, tvar)] = tvar
        for p, tp in zip(ps, tps):
            set_type(p, tp)
        prop_body(b)
        return cft
    return in_new_scope(cret, inside_func_scope)

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
    check_expr(CData(extrinsic(FieldDT, f), []), s) # XXX
    return ft

def prop_getenv(environ):
    return stuff

def prop_inenv(environ, init, f):
    return stuff

def unknown_prop(a):
    assert False, with_context('Unknown prop case:\n%s' % (a,))

def prop_expr(e):
    return match(e,
        ("IntLit(_)", lambda: CPrim(PInt())),
        ("StrLit(_)", lambda: CPrim(PStr())),
        ("TupleLit(ts)", lambda ts: CTuple(map(prop_expr, ts))),
        ("ListLit(ss)", lambda ts: CList(map(prop_expr, ts))),
        ("Call(f, s)", prop_call),
        ("And(l, r)", prop_logic),
        ("Or(l, r)", prop_logic),
        ("e==FuncExpr(f==Func(ps, b))", prop_func),
        ("m==Match(p, cs)", prop_match),
        ("Attr(s, f==Field(ft))", prop_attr),
        ("GetCtxt(environ)", prop_getenv),
        ("InCtxt(environ, init, f)", prop_inenv),
        ("ref==Bind(b)", prop_binding),
        ("_", lambda: unknown_prop(e)))

def check_expr(t, e):
    unify(t, prop_expr(e))

def check_lhs(tv, lhs):
    in_env(PROP, tv, lambda: match(lhs,
        ("LhsAttr(s, f)", lambda s, f: check_attr_lhs(s, f, lhs)),
        ("LhsVar(v)", lambda v: unify_m(instantiate(v, tv))),
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
        set_type(c, TFunc(fieldTs, dtT))

def prop_new_env(environ):
    # TODO
    pass

def prop_new_extrinsic(ext):
    # XXX: Should have a declarative area for this kind of stuff
    #      so I can unify all this lookup business
    pass

def prop_defn(a, e):
    set_type(a, generalize_type(prop_expr(e)))

def prop_assign(a, e):
    t = prop_lhs(a)
    check_expr(t, e)

def prop_augassign(a, e):
    check_lhs(CInt(), a)
    check_expr(CInt(), e)

def prop_cond(cases, else_):
    for t, b in cases:
        check_expr(CBool(), t)
        prop_body(b)
    if isJust(else_):
        prop_body(fromJust(else_))

def prop_while(test, body):
    check_expr(CBool(), test)
    prop_body(body)

def prop_assert(tst, msg):
    check_expr(CBool(), tst)
    check_expr(CStr(), msg)

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
