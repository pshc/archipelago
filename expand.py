#!/usr/bin/env python2
from base import *
from atom import *
import globs

FlowNode = DT('FlowNode', ('outflows', 'set([FlowNode])'),
                          ('returns', bool))

VarKind, FuncLocal, FormalParam = ADT('VarKind', 'FuncLocal', 'FormalParam')

ExScope = DT('ExScope', ('curFlow', FlowNode),
                        ('pendingFlows', ['*FlowNode']),
                        ('localVars', {'*Var': VarKind}),
                        ('prevScope', 'Maybe(*ExScope)'))

EXSCOPE = new_env('EXSCOPE', ExScope)

ExFunc, ExStaticDefn, ExInnerFunc = ADT('ExFunc',
        'ExStaticDefn',
        'ExInnerFunc', ('closedVars', 'set([*Var])'),
                       ('outerFunc', '*ExFunc'))

EXFUNC = new_env('EXFUNC', ExFunc)

ExGlobal = DT('ExGlobal', ('curTopLevel', '*TopLevel'),
                          ('module', '*Module'))

EXGLOBAL = new_env('EXGLOBAL', ExGlobal)

IMPORTBINDS = new_env('IMPORTBINDS', set(['a'])) # Bindable

ExCode, ExSurfacedFunc, ExStrLit = ADT('ExCode',
        'ExSurfacedFunc', ('func', Func),
        'ExStrLit', ('var', Var), ('str', str))

Expansion = new_extrinsic('Expansion', [ExCode])

ClosureInfo = DT('ClosureInfo', ('func', Func), ('isClosure', bool))
Closure = new_extrinsic('Closure', ClosureInfo)

ExpandedDeclInfo = DT('ExpandedDeclInfo', ('var', '*Var'))
ExpandedDecl = new_extrinsic('ExpandedDecl', ExpandedDeclInfo)

VarUsageInfo = DT('VarUsageInfo', ('isReassigned', bool))
VarUsage = new_extrinsic('VarUsage', VarUsageInfo)

VarInfo = DT('VarInfo', ('function', ExFunc))
LocalVar = new_extrinsic('LocalVar', VarInfo)

CtorIndex = new_extrinsic('CtorIndex', int)
FieldIndex = new_extrinsic('FieldIndex', int)

LayoutInfo = DT('LayoutInfo', ('extrSlot', 'Maybe(int)'),
                              ('discrimSlot', 'Maybe(int)'))
DataLayout = new_extrinsic('DataLayout', LayoutInfo)

def top_scope():
    return ExScope(new_flow(), [], {}, Nothing())

def in_new_scope(f, innerFlow):
    oldScope = env(EXSCOPE)
    s = ExScope(innerFlow, [], {}, Just(oldScope))
    ret = in_env(EXSCOPE, s, f)
    oldScope.pendingFlows += s.pendingFlows
    return ret

def new_flow():
    return FlowNode(set(), False)

def cur_flow():
    return env(EXSCOPE).curFlow

def activate_flow(newFlow):
    scope = env(EXSCOPE)
    scope.curFlow = newFlow
    if len(scope.pendingFlows) > 0:
        for flow in scope.pendingFlows:
            flow.outflows.add(newFlow)
        scope.pendingFlows = []

def add_outflows(flow, outflows):
    flow.outflows.update(outflows)

def push_expansion(ex):
    top = env(EXGLOBAL).curTopLevel
    if not has_extrinsic(Expansion, top):
        add_extrinsic(Expansion, top, [])
    extrinsic(Expansion, top).append(ex)

def ex_strlit(lit, s):
    v = Var()
    add_extrinsic(Name, v, '.LC%d' % (extrinsic(Location, lit).index,))
    push_expansion(ExStrLit(v, s))
    add_extrinsic(ExpandedDecl, lit, ExpandedDeclInfo(v))

def ex_call(f, args):
    ex_expr(f)
    map_(ex_expr, args)

def ex_logic(l, r):
    ex_expr(l)
    ex_expr(r)

def ex_ternary(c, t, f):
    ex_expr(c)
    ex_expr(t)
    ex_expr(f)

def ex_funcexpr(f):
    info = ex_func(f.params, f.body)
    isClosure = len(info.closedVars) > 0
    push_expansion(ExSurfacedFunc(f))
    add_extrinsic(Closure, f, ClosureInfo(f, isClosure))

def ex_match_case(c):
    pass

def ex_match(m, e, cs):
    ex_expr(e)
    for c in cs:
        ex_match_case(c)

def ex_getenv(environ):
    pass

def ex_inenv(environ, init, f):
    ex_expr(init)
    ex_expr(f)

def ex_bind(target):
    if extrinsic(Location, target).module is not env(EXGLOBAL).module:
        env(IMPORTBINDS).add(target)
    v = Bindable.isVar(target)
    if isJust(v):
        ex_bind_var(fromJust(v))

def ex_bind_var(v):
    m = match(env(EXFUNC))
    if m('f==ExInnerFunc(closVars, _)'):
        f, closVars = m.args
        if has_extrinsic(LocalVar, v):
            assert isinstance(v, Var)
            info = extrinsic(LocalVar, v)
            if info.function != f:
                closVars.add(v)

def ex_expr(e):
    match(e,
        ("IntLit(_) or FloatLit(_)", nop),
        ("lit==StrLit(s)", ex_strlit),
        ("Call(f, args)", ex_call),
        ("And(l, r) or Or(l, r)", ex_logic),
        ("Ternary(c, t, f)", ex_ternary),
        ("FuncExpr(f)", ex_funcexpr),
        ("TupleLit(ts)", lambda ts: map_(ex_expr, ts)),
        ("ListLit(ls)", lambda ls: map_(ex_expr, ls)),
        ("m==Match(e, cases)", ex_match),
        ("Attr(e, _)", ex_expr),
        ("GetEnv(environ)", ex_getenv),
        ("HaveEnv(_)", nop),
        ("InEnv(environ, i, e)", ex_inenv),
        ("GetExtrinsic(_, node)", ex_expr),
        ("HasExtrinsic(_, node)", ex_expr),
        ("ScopeExtrinsic(_, f)", ex_expr),
        ("Bind(target)", ex_bind))

def ex_pat_var(v):
    # a little redundant...
    add_extrinsic(LocalVar, v, VarInfo(env(EXFUNC)))
    env(EXSCOPE).localVars[v] = FuncLocal()

def ex_pat(pat):
    match(pat, ("PatVar(v)", ex_pat_var),
               ("PatTuple(ps)", lambda ps: map_(ex_pat, ps)))

def ex_func_defn(v, e, f):
    add_extrinsic(Name, f, extrinsic(Name, v))
    ex_pat_var(v)
    ex_expr(e)

def ex_defn(pat, e):
    ex_pat(pat)
    ex_expr(e)

def ex_assign(a, e):
    ex_expr(e) # Must come first!
    ex_lhs(a)

def ex_lhs(a):
    match(a,
        ("LhsVar(v)", ex_lhs_var),
        ("LhsAttr(s, _)", ex_expr))

def ex_lhs_var(v):
    # close over in this scope
    ex_bind_var(v)
    if not has_extrinsic(VarUsage, v):
        add_extrinsic(VarUsage, v, VarUsageInfo(True))

def ex_flow(s, b, top):
    s.flowFrom = [top]
    ex_body(b)

def ex_cond(cs):
    incomingFlow = cur_flow()
    for case in cs:
        ex_expr(case.test)
        flow = new_flow()
        add_outflows(incomingFlow, set([flow]))
        in_new_scope(lambda: ex_body(case.body), flow)

def ex_while(t, b):
    incomingFlow = cur_flow()
    ex_expr(t)
    flow = new_flow()
    in_new_scope(lambda: ex_body(b), flow)

def ex_assert(t, m):
    ex_expr(t)
    ex_expr(m)

def ex_func(params, b):
    def go():
        scope = env(EXSCOPE)
        for p in params:
            scope.localVars[p] = FormalParam()
        ex_body(b)
        for endingScope in scope.pendingFlows:
            endingScope.returns = True
        scope.pendingFlows = []
    fc = ExInnerFunc(set(), env(EXFUNC))
    in_new_scope(lambda: in_env(EXFUNC, fc, go), new_flow())
    return fc

def ex_return(e):
    ex_expr(e)
    cur_flow().returns = True

def ex_returnnothing():
    cur_flow().returns = True

def ex_writeextrinsic(node, val):
    ex_expr(node)
    ex_expr(val)

def ex_stmt(s):
    match(s,
        ("ExprStmt(e)", ex_expr),
        ("Defn(PatVar(v), e==FuncExpr(f))", ex_func_defn),
        ("Defn(pat, e)", ex_defn),
        ("Assign(lhs, e)", ex_assign),
        ("AugAssign(_, lhs, e)", ex_assign),
        ("Break() or Continue()", nop),
        ("Cond(cases)", ex_cond),
        ("While(t, b)", ex_while),
        ("Assert(t, m)", ex_assert),
        ("Return(e)", ex_return),
        ("ReturnNothing()", ex_returnnothing),
        ("WriteExtrinsic(_, node, val, _)", ex_writeextrinsic))

def ex_body(body):
    map_(ex_stmt, body.stmts)

def ex_top_func(v, f):
    add_extrinsic(Name, f, extrinsic(Name, v))
    in_env(EXFUNC, ExStaticDefn(), lambda: ex_func(f.params, f.body))

def ex_top_defn(e):
    in_env(EXFUNC, ExStaticDefn(), lambda: ex_expr(e))

def ex_dt(dt):
    discrim = len(dt.ctors) > 1
    info = LayoutInfo(Just(0), Just(1) if discrim else Nothing())
    add_extrinsic(DataLayout, dt, info)
    base = 2 if discrim else 1
    for i, ctor in enumerate(dt.ctors):
        add_extrinsic(CtorIndex, ctor, i)
        for ix, field in enumerate(ctor.fields):
            add_extrinsic(FieldIndex, field, ix + base)

def ex_top_level(s):
    match(s,
        ("TopCDecl(_)", nop),
        ("TopDefn(PatVar(v), FuncExpr(f))", ex_top_func),
        ("TopDefn(_, e)", ex_top_defn),
        ("TopDT(dt)", ex_dt),
        ("TopEnv(_)", nop),
        ("TopExtrinsic(_)", nop))

def in_intramodule_env(func):
    captures = {}
    extrs = [Expansion, Closure, ExpandedDecl, VarUsage]
    return in_env(IMPORTBINDS, set(),
            lambda: capture_scoped(extrs, captures, func))

def in_intermodule_env(func):
    captures = {}
    extrs = [DataLayout, CtorIndex, FieldIndex]
    return capture_scoped(extrs, captures, func)

def expand_module(mod):
    def go():
        eg = env(EXGLOBAL)
        for top in mod.root.tops:
            eg.curTopLevel = top
            in_env(EXSCOPE, top_scope(), lambda: ex_top_level(top))
    captures = {}
    in_env(EXGLOBAL, ExGlobal(None, mod),
            lambda: scope_extrinsic(LocalVar, go))
    return captures

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
