#!/usr/bin/env python2
from base import *
from atom import *
import globs

FlowNode = DT('FlowNode', ('outflows', 'set([FlowNode])'),
                          ('returns', bool))

VarLifetime = DT('VarLifetime', ('staticCtr', int))

VarUse = DT('VarUse', ('useIndex', int))

ExScope = DT('ExScope', ('curFlow', FlowNode),
                        ('pendingFlows', ['*FlowNode']),
                        ('formalParams', ['*Var']),
                        ('localVars', {'*Var': '*Var'}),
                        ('closedVars', {'*Var': '*Var'}),
                        ('funcScope', 'Maybe(ExScope)'),
                        ('prevScope', 'Maybe(ExScope)'))

EXSCOPE = new_context('EXSCOPE', ExScope)

ExGlobal = DT('ExGlobal', ('egCurTopLevel', TopLevel),
                          ('egFuncAugs', {'*Stmt': ['*Stmt']}),
                          ('egTypeAugs', {'*Stmt': '*Expr'}),
                          ('egLambdaRefs', {'*Expr': '*Stmt'}),
                          ('egVarLifetime', {'*Var': VarLifetime}),
                          ('egVarUses', {'*Var': VarUse}))

EXGLOBAL = new_context('EXGLOBAL', ExGlobal)

def init_global():
    return ExGlobal(None, {}, {}, {}, {}, {})

def top_scope():
    return ExScope(new_flow(), [], [], {}, {}, Nothing(), Nothing())

def in_new_scope(f, innerFlow):
    def go():
        ret = f(context(EXSCOPE))
        return ret

    oldScope = context(EXSCOPE)
    s = ExScope(innerFlow, [], [], {}, {}, oldScope.funcScope, Just(oldScope))
    return in_context(EXSCOPE, s, go)

def new_flow():
    return FlowNode(set(), False)

def cur_flow():
    return context(EXSCOPE).curFlow

def activate_flow(flow):
    context(EXSCOPE).curFlow = flow

def add_outflows(flow, outflows):
    flow.outflows.update(outflows)

def ex_call(f, args):
    ex_expr(f)
    map_(ex_expr, args)

def ex_lambda(lam, args, e):
    # Closure time
    nm = symname('lambda_func')
    fargs = [int_len(args)] + args

    eg = context(EXGLOBAL)

    for a in args:
        eg.egVarLifetime[a] = VarLifetime(0)

    def lam_body(scope):
        scope.formalParams = args
        ex_expr(e)
    flow = new_flow()
    in_new_scope(lam_body, flow)

    fbody = [int_(1), symref('return', [symref('xref', [ref_(e)])])]
    f = symref('func', [nm, symref('args', fargs), symref('body', fbody)])

    key = eg.egCurTopLevel

    if key not in eg.egFuncAugs:
        eg.egFuncAugs[key] = []
    eg.egFuncAugs[key].append(f)
    eg.egTypeAugs[f] = lam
    eg.egLambdaRefs[lam] = f

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

def ex_var(r, v):
    eg = context(EXGLOBAL)
    life = eg.egVarLifetime[v]
    eg.egVarUses[r] = VarUse(life.staticCtr)

def ex_unknown_expr(e):
    assert False, 'Unknown expr for expansion:\n' + repr(e)

def ex_expr(e):
    match(e,
        ("IntLit(_)", nop),
        ("StrLit(_)", nop),
        ("Call(f, args)", ex_call),
        ("lam==Lambda(params, e)", ex_lambda),
        ("TupleLit(ts)", lambda ts: map_(ex_expr, ts)),
        ("ListLit(ls)", lambda ls: map_(ex_expr, ls)),
        ("m==Match(e, cases)", ex_match),
        ("Attr(e, _)", ex_expr),
        ("GetCtxt(ctxt)", ex_getctxt),
        ("InCtxt(ctxt, i, e)", ex_inctxt),
        ("r==Bind(BindVar(v))", ex_var),
        ("Bind(BindFunc(_) or BindCtor(_) or BindBuiltin(_))", nop),
        ("otherwise", ex_unknown_expr))

def ex_defn(v, e):
    context(EXGLOBAL).egVarLifetime[v] = VarLifetime(0)
    context(EXSCOPE).localVars[v] = None # What to store?
    ex_expr(e)

def ex_assign(a, e):
    ex_expr(e) # Must come first!
    ex_lhs(a)

def ex_lhs(a):
    match(a,
        ("LhsAttr(s, _)", ex_lhs),
        ("LhsVar(v)", ex_lhs_var))

def ex_lhs_var(v):
    context(EXGLOBAL).egVarLifetime[v].staticCtr += 1
    destScope = context(EXSCOPE)
    scope = Just(destScope)
    while True:
        assert isJust(scope), "Never-defined local var " + repr(v)
        s = fromJust(scope)
        if v in s.localVars:
            # TODO
            #destScope.assignments[v] = s
            return
        scope = s.prevScope

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

def ex_func(f, args, b):
    eg = context(EXGLOBAL)
    for a in args:
        eg.egVarLifetime[a] = VarLifetime(0)

    def f_body(scope):
        scope.formalParams = args
        scope.funcScope = Just(scope)
        ex_body(b)
    in_new_scope(f_body, new_flow())

def ex_return(e):
    ex_expr(e)
    cur_flow().returns = True
    # New flow is guaranteed dead. Blah. But OK for now.
    # (Avoiding dead code removal for now for debugability)
    activate_flow(new_flow())

def ex_returnnothing():
    cur_flow().returns = True
    activate_flow(new_flow())

def ex_stmt(s):
    match(s,
        ("ExprStmt(e)", ex_expr),
        ("Defn(var, e)", ex_defn),
        ("Assign(lhs, e)", ex_assign),
        ("AugAssign(_, lhs, e)", ex_assign),
        ("Cond(cases, elseCase)", ex_cond),
        ("While(t, b)", ex_while),
        ("Assert(t, m)", ex_assert),
        ("FuncStmt(f==Func(args, b))", ex_func),
        ("Return(e)", ex_return),
        ("ReturnNothing()", ex_returnnothing))

def nop():
    pass

def ex_body(body):
    map_(ex_stmt, body.stmts)

def ex_top_level(s):
    match(s,
        ("TopDefn(var, e)", ex_defn),
        ("TopFunc(f==Func(args, b))", ex_func),
        ("TopDT(_)", nop),
        ("TopCtxt(_)", nop),
        ("TopExtrinsic(_)", nop))

def expand_module(mod):
    def go():
        eg = context(EXGLOBAL)
        for top in mod.root.tops:
            eg.egCurTopLevel = top
            in_context(EXSCOPE, top_scope(), lambda: ex_top_level(top))
        return {'func': eg.egFuncAugs,
                'type': eg.egTypeAugs,
                'lambda': eg.egLambdaRefs}
    return in_context(EXGLOBAL, init_global(), go)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
