from atom import *
from astconv import AstHint, AstType

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

def scan_ternary(c, t, f):
    scan_expr(c)
    scan_expr(t)
    scan_expr(f)

def scan_func(f, ps, b):
    if not has_extrinsic(AstType, f):
        scan_body(b)
        return

    tvars = {}
    ftstr, ftmeta = extrinsic(AstType, f)
    ft = parse_new_type(ftstr, tvars)
    ft.meta = ftmeta
    tps = ft.paramTypes
    assert len(tps) == len(ps), "Mismatched param count: %s\n%s" % (tps, ps)
    set_type(f, ft)

    closed = env(INWARD).closedVars
    closed.update(tvars)
    in_env(INWARD, Inward(closed), lambda: scan_body(b))

def scan_match():
    pass

def scan_attr(s, f):
    # Can't resolve f without type info. Deferred to prop for now.
    scan_expr(s)

def scan_inenv(init, f):
    scan_expr(init)
    scan_expr(f)

# Augment AST with instantiation records

INSTSUSED = new_env('INSTSUSED', {TypeVar: Type})

def record_tvar(tv):
    insts = env(INSTSUSED)
    if tv not in insts:
        nm = extrinsic(Name, tv)
        it = env(INWARD).closedVars.get(nm)
        if it is not None:
            insts[tv] = in_env(TVARS, {nm: tv}, lambda: parse_type(it))

def scan_inst_data(tvs, apps):
    map_(record_tvar, tvs)
    map_(scan_inst, apps)

def scan_inst_func(ps, r):
    map_(scan_inst, ps)
    if matches(r, ('Ret(_)')):
        scan_inst(r.type)

def scan_inst(s):
    match(s,
        ('TVar(tv)', record_tvar),
        ('TPrim(_)', nop),
        ('TTuple(ts)', lambda ts: map_(scan_inst, ts)),
        ('TFunc(ps, r, _)', scan_inst_func),
        ('TData(DataType(_, tvs, _), apps)', scan_inst_data),
        ('TArray(t)', scan_inst),
        ('TWeak(t)', scan_inst))

def instantiate_type(site, t):
    insts = {}
    in_env(INSTSUSED, insts, lambda: scan_inst(t))
    for k in insts.keys():
        if insts[k] is None:
            del insts[k]
    #if insts:
    #    add_extrinsic(InstMap, site, insts)

def instantiate(site, v):
    if has_extrinsic(TypeOf, v):
        instantiate_type(site, extrinsic(TypeOf, v))

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
        ("Lit(_)", nop),
        ("TupleLit(ts)", lambda ts: map_(scan_expr, ts)),
        ("ListLit(ss)", lambda ss: map_(scan_expr, ss)),
        ("Call(f, s)", scan_call),
        ("And(l, r) or Or(l, r)", scan_logic),
        ("Ternary(c, t, f)", scan_ternary),
        ("FuncExpr(f==Func(ps, b))", scan_func),
        ("Match(_, _)", scan_match),
        ("Attr(s, f)", scan_attr),
        ("GetEnv(_)", nop),
        ("HaveEnv(_)", nop),
        ("InEnv(_, init, f)", scan_inenv),
        ("GetExtrinsic(_, e)", scan_expr),
        ("HasExtrinsic(_, e)", scan_expr),
        ("ScopeExtrinsic(_, f)", scan_expr),
        ("e==Bind(b)", instantiate)))

def scan_lhs_attr(e, f):
    scan_expr(e)
    # Ideally with type info here we would fix f. Deferred to prop for now.

def scan_lhs(lhs):
    match(lhs,
        ("lhs==LhsVar(v)", instantiate),
        ("LhsAttr(e, f)", scan_lhs_attr))

def scan_assign(lhs, e):
    scan_lhs(lhs)
    scan_expr(e)

def scan_augassign(lhs, e):
    scan_lhs(lhs)
    scan_expr(e)

def scan_cond(cases):
    for case in cases:
        scan_expr(case.test)
        scan_body(case.body)

def scan_while(t, b):
    scan_expr(t)
    scan_body(b)

def scan_assert(t, m):
    scan_expr(t)
    scan_expr(m)

def scan_writeextrinsic(e, val):
    scan_expr(e)
    scan_expr(val)

def scan_stmt(stmt):
    in_env(STMTCTXT, stmt, lambda: match(stmt,
        ("Defn(_, e)", scan_expr),
        ("Assign(lhs, e)", scan_assign),
        ("AugAssign(_, lhs, e)", scan_augassign),
        ("Break() or Continue()", nop),
        ("Cond(cases)", scan_cond),
        ("Discard(e)", scan_expr),
        ("While(t, b)", scan_while),
        ("Assert(t, m)", scan_assert),
        ("Return(e)", scan_expr),
        ("ReturnNothing()", nop),
        ("WriteExtrinsic(_, e, val, _)", scan_writeextrinsic),
        ("VoidCall(f, args)", scan_call)))

def scan_body(body):
    map_(scan_stmt, body.stmts)

def scan_compilation_unit(unit):
    for f in unit.funcs:
        in_env(STMTCTXT, f, lambda:
                match(f, ("TopFunc(_, f==Func(ps, b))", scan_func)))

def scan_root(root):
    in_env(INWARD, Inward({}), lambda: scan_compilation_unit(root))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
