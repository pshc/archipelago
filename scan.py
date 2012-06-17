from atom import *
from ast import AstHint, AstType

Inward = DT('Inward', ('closedVars', {'*TypeVar': Type}))
INWARD = new_env('INWARD', Inward)

def set_type(e, t):
    assert isinstance(t, Type), "%s is not a type" % (t,)
    add_extrinsic(TypeOf, e, t)

def scan_call(f, args):
    scan_expr(f)
    for arg in args:
        scan_expr(arg)

def scan_logic(l, r):
    scan_expr(l)
    scan_expr(r)

def scan_func(f, ps, b):
    tvars = {}
    ft = parse_new_type(extrinsic(AstType, f), tvars)
    tps, tret = match(ft, ('TFunc(tps, tret)', tuple2))
    assert len(tps) == len(ps), "Mismatched param count: %s\n%s" % (tps, ps)
    set_type(f, ft)

    closed = env(INWARD).closedVars
    closed.update(tvars)
    in_env(INWARD, Inward(closed), lambda: scan_body(b))

def scan_match():
    pass

def scan_attr(s, f, ft):
    scan_expr(s)

def scan_getenv(e):
    pass

def scan_inenv(e, init, f):
    scan_expr(init)
    scap_expr(f)

def instantiate_type(site, t):
    closed = env(INWARD).closedVars
    insts = {}
    def _inst_tvar(ref):
        tv = match(ref, ("TVar(tv)", identity))
        if tv not in insts:
            nm = extrinsic(Name, tv)
            it = closed.get(nm)
            if it is not None:
                insts[tv] = in_env(TVARS, closed, lambda: parse_type(it))
        return ref
    map_type_vars(_inst_tvar, t)
    if insts:
        add_extrinsic(InstMap, site, insts)
    return t

def instantiate(site, v):
    if has_extrinsic(TypeOf, v):
        return instantiate_type(site, extrinsic(TypeOf, v))

def scan_binding(b):
    # Typeclasses would be nice
    return match(b,
        ("s==BindVar(v)", instantiate),
        ("s==BindCtor(c)", instantiate),
        ("s==BindBuiltin(b)", instantiate))

def scan_expr(e):
    if has_extrinsic(AstHint, e):
        old = env(INWARD).closedVars
        new = extrinsic(AstHint, e)
        for k, v in new.iteritems():
            if k not in old or old[k] != v:
                up = old.copy()
                up.update(new)
                in_env(INWARD, Inward(up), lambda: _scan_expr(e))
                return
    _scan_expr(e)

def _scan_expr(e):
    in_env(EXPRCTXT, e, lambda: match(e,
        ("IntLit(_) or StrLit(_)", nop),
        ("TupleLit(ts)", lambda ts: map_(scan_expr, ts)),
        ("ListLit(ss)", lambda ss: map_(scan_expr, ss)),
        ("Call(f, s)", scan_call),
        ("And(l, r) or Or(l, r)", scan_logic),
        ("FuncExpr(f==Func(ps, b))", scan_func),
        ("Match(_, _)", scan_match),
        ("Attr(s, f==Field(ft))", scan_attr),
        ("GetEnv(env)", scan_getenv),
        ("InEnv(env, init, f)", scan_inenv),
        ("Bind(b)", scan_binding)))

def scan_assign(lhs, e):
    scan_expr(e)

def scan_augassign(lhs, e):
    scan_expr(e)

def scan_cond(cases, else_):
    for case in cases:
        scan_expr(case.test)
        scan_body(case.body)
    if isJust(else_):
        scan_body(fromJust(else_))

def scan_while(t, b):
    scan_expr(t)
    scan_body(b)

def scan_assert(t, m):
    scan_expr(t)
    scan_expr(m)

def scan_stmt(stmt):
    in_env(STMTCTXT, stmt, lambda: match(stmt,
        ("Defn(var, e)", scan_defn),
        ("Assign(lhs, e)", scan_assign),
        ("AugAssign(_, lhs, e)", scan_augassign),
        ("Break()", nop),
        ("ExprStmt(e)", scan_expr),
        ("Cond(cases, elseCase)", scan_cond),
        ("While(t, b)", scan_while),
        ("Assert(t, m)", scan_assert),
        ("Return(e)", scan_expr),
        ("ReturnNothing()", nop)))

def scan_body(body):
    map_(scan_stmt, body.stmts)

def scan_defn(var, e):
    scan_expr(e)

def scan_top_level(a):
    in_env(STMTCTXT, a, lambda: match(a,
        ("TopDefn(var, e)", scan_defn),
        ("_", nop)))

def scan_compilation_unit(unit):
    map_(scan_top_level, unit.tops)

def scan_root(root):
    in_env(INWARD, Inward({}), lambda: scan_compilation_unit(root))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
