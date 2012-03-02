#!/usr/bin/env python2
from base import *
from atom import *
import globs

FlowNode = DT('FlowNode', ('outflows', 'set([FlowNode])'),
                          ('returns', bool))

VarKind, LocalVar, FormalParam = ADT('VarKind', 'LocalVar', 'FormalParam')

ExScope = DT('ExScope', ('curFlow', FlowNode),
                        ('pendingFlows', ['*FlowNode']),
                        ('localVars', {'*Var': VarKind}),
                        ('closedVars', {'*Var': '*Var'}),
                        ('funcScope', 'Maybe(ExScope)'),
                        ('prevScope', 'Maybe(ExScope)'))

EXSCOPE = new_context('EXSCOPE', ExScope)

ExGlobal = DT('ExGlobal', ('egCurTopLevel', TopLevel))

EXGLOBAL = new_context('EXGLOBAL', ExGlobal)

ExCode = DT('ExCode', ('tops', [TopLevel]))
Expansion = new_extrinsic('Expansion', ExCode)

ClosureInfo = DT('ClosureInfo', ('func', Func))
Closure = new_extrinsic('Closure', ClosureInfo)

VarInfo = DT('VarInfo', ('scope', ExScope))
LocalVar = new_extrinsic('LocalVar', VarInfo)

def top_scope():
    return ExScope(new_flow(), [], {}, {}, Nothing(), Nothing())

def in_new_scope(f, innerFlow):
    oldScope = context(EXSCOPE)
    s = ExScope(innerFlow, [], {}, {}, oldScope.funcScope, Just(oldScope))
    ret = in_context(EXSCOPE, s, lambda: f(context(EXSCOPE)))
    oldScope.pendingFlows += s.pendingFlows
    return ret

def new_flow():
    return FlowNode(set(), False)

def cur_flow():
    return context(EXSCOPE).curFlow

def activate_flow(newFlow):
    scope = context(EXSCOPE)
    scope.curFlow = newFlow
    if len(scope.pendingFlows) > 0:
        for flow in scope.pendingFlows:
            flow.outflows.add(newFlow)
        scope.pendingFlows = []

def add_outflows(flow, outflows):
    flow.outflows.update(outflows)

def ex_call(f, args):
    ex_expr(f)
    map_(ex_expr, args)

def ex_funcexpr(fe, f, params, body):
    ex_func(params, body)

    key = context(EXGLOBAL).egCurTopLevel

    if not has_extrinsic(Expansion, key):
        add_extrinsic(Expansion, key, [])
    extrinsic(Expansion, key).append(f)
    add_extrinsic(Closure, fe, ClosureInfo(f))

def ex_match_case(c):
    pass

def ex_match(m, e, cs):
    ex_expr(e)
    for c in cs:
        ex_match_case(c)

def ex_getctxt(ctxt):
    pass

def ex_inctxt(ctxt, init, f):
    ex_expr(init)
    ex_expr(f)

def ex_bind_var(b, v):
    # TODO: Close over this var in all active closures
    v

def ex_unknown_expr(e):
    assert False, 'Unknown expr for expansion:\n' + repr(e)

def ex_expr(e):
    match(e,
        ("IntLit(_)", nop),
        ("StrLit(_)", nop),
        ("Call(f, args)", ex_call),
        ("fe==FuncExpr(f==Func(params, body))", ex_funcexpr),
        ("TupleLit(ts)", lambda ts: map_(ex_expr, ts)),
        ("ListLit(ls)", lambda ls: map_(ex_expr, ls)),
        ("m==Match(e, cases)", ex_match),
        ("Attr(e, _)", ex_expr),
        ("GetCtxt(ctxt)", ex_getctxt),
        ("InCtxt(ctxt, i, e)", ex_inctxt),
        ("b==Bind(BindVar(v))", ex_bind_var),
        ("Bind(BindFunc(_) or BindCtor(_) or BindBuiltin(_))", nop),
        ("otherwise", ex_unknown_expr))

def ex_defn(v, e):
    add_extrinsic(LocalVar, v, VarInfo(context(EXSCOPE)))
    ex_expr(e)

def ex_top_defn(v, e):
    # v is considered static, don't close over
    ex_expr(e)

def ex_assign(a, e):
    ex_expr(e) # Must come first!
    ex_lhs(a)

def ex_lhs(a):
    match(a,
        ("LhsAttr(s, _)", ex_lhs),
        ("LhsVar(v)", ex_lhs_var))

def ex_lhs_var(v):
    if has_extrinsic(LocalVar, v):
        # TODO: close over v in this scope too
        info = extrinsic(LocalVar, v)

def ex_flow(s, b, top):
    s.flowFrom = [top]
    ex_body(b)

def ex_cond(cond, ss, cs):
    incomingFlow = cur_flow()
    for t, b in cs:
        ex_expr(t)
        flow = new_flow()
        add_outflows(incomingFlow, set([flow]))
        in_new_scope(lambda s: ex_body(b), flow)
    eb = match(ss, ("contains(key('else', sized(body)))", Just),
                   ("_", Nothing))
    if isJust(eb):
        flow = new_flow()
        add_outflows(incomingFlow, set([flow]))
        in_new_scope(lambda s: ex_body(fromJust(eb)), flow)
    activate_flow(outgoingFlow)

def ex_while(t, b):
    incomingFlow = cur_flow()
    ex_expr(t)
    flow = new_flow()
    in_new_scope(lambda s: ex_body(b), flow)

def ex_assert(t, m):
    ex_expr(t)
    ex_expr(m)

def ex_func(params, b):
    def go(scope):
        scope.funcScope = Just(scope)
        for p in params:
            scope.localVars[p] = FormalParam()
        ex_body(b)
        for endingScope in scope.pendingFlows:
            endingScope.returns = True
        scope.pendingFlows = []
    in_new_scope(go, new_flow())

def ex_return(e):
    ex_expr(e)
    cur_flow().returns = True

def ex_returnnothing():
    cur_flow().returns = True

def ex_stmt(s):
    match(s,
        ("ExprStmt(e)", ex_expr),
        ("Defn(var, e)", ex_defn),
        ("Assign(lhs, e)", ex_assign),
        ("AugAssign(_, lhs, e)", ex_assign),
        ("Cond(cases, elseCase)", ex_cond),
        ("While(t, b)", ex_while),
        ("Assert(t, m)", ex_assert),
        ("Return(e)", ex_return),
        ("ReturnNothing()", ex_returnnothing))

def nop():
    pass

def ex_body(body):
    map_(ex_stmt, body.stmts)

def ex_top_level(s):
    match(s,
        ("TopDefn(var, e)", ex_top_defn),
        ("TopFunc(Func(params, b))", ex_func),
        ("TopDT(_)", nop),
        ("TopCtxt(_)", nop),
        ("TopExtrinsic(_)", nop))

def expand_module(mod):
    def go():
        eg = context(EXGLOBAL)
        for top in mod.root.tops:
            eg.egCurTopLevel = top
            in_context(EXSCOPE, top_scope(), lambda: ex_top_level(top))
    captures = {}
    in_context(EXGLOBAL, ExGlobal(None),
            lambda: scope_extrinsic(LocalVar,
            lambda: capture_scoped([Expansion, Closure], captures, go)))
    return captures

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
