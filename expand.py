#!/usr/bin/env python2
from base import *
from atom import *
import globs

FlowNode = DT('FlowNode', ('outflows', 'set([FlowNode])'),
                          ('returns', bool))

ExScope = DT('ExScope', ('curFlow', 'FlowNode'),
                        ('formalParams', [Atom]),
                        ('localVars', {Atom: Atom}),
                        ('closedVars', {Atom: Atom}),
                        ('funcScope', 'Maybe(ExScope)'),
                        ('prevScope', 'Maybe(ExScope)'))

EXSCOPE = Nothing()

ExGlobal = DT('ExGlobal', ('egCurTopLevelDecl', Atom),
                          ('egFuncAugs', {Atom: Atom}),
                          ('egTypeAugs', {Atom: Atom}),
                          ('egLambdaRefs', {Atom: Atom}),
                          ('egVarLifetime', {Atom: Atom}),
                          ('egVarUses', {Atom: Atom}))

EXGLOBAL = Nothing()

VarLifetime = DT('VarLifetime', ('staticCtr', int))

VarUse = DT('VarUse', ('useIndex', int))

def setup_ex_env(roots):
    global EXSCOPE
    EXSCOPE = Nothing()
    global EXGLOBAL
    EXGLOBAL = Just(ExGlobal(roots[0], {}, {}, {}, {}, {}))

def in_new_scope(f, inflow, outflows):
    global EXSCOPE
    surroundingFunc = mapMaybe(lambda s: s.funcScope, EXSCOPE)
    s = ExScope(inflow, [], {}, {}, surroundingFunc, EXSCOPE)
    EXSCOPE = Just(s)
    ret = f(s)
    assert s is EXSCOPE.just, "Scope inconsistency"
    # the last flow in this scope exits to the outer scope
    add_outflows(s.curFlow, outflows)
    EXSCOPE = s.prevScope
    return ret

def new_flow():
    return FlowNode(set(), False)

def cur_flow():
    global EXSCOPE
    return fromJust(EXSCOPE).curFlow

def activate_flow(flow):
    global EXSCOPE
    fromJust(EXSCOPE).curFlow = flow

def add_outflows(flow, outflows):
    flow.outflows.update(outflows)

def ex_call(f, args):
    ex_expr(f)
    map_(ex_expr, args)

def ex_lambda(lam, args, e):
    # Closure time
    nm = symname('lambda_func')
    fargs = [int_len(args)] + args

    global EXGLOBAL
    eg = fromJust(EXGLOBAL)

    for a in args:
        eg.egVarLifetime[a] = VarLifetime(0)

    def lam_body(scope):
        scope.formalParams = args
        ex_expr(e)
    flow = new_flow()
    in_new_scope(lam_body, flow, set())

    fbody = [int_(1), symref('return', [symref('xref', [ref_(e)])])]
    f = symref('func', [nm, symref('args', fargs), symref('body', fbody)])

    key = eg.egCurTopLevelDecl

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
    global EXGLOBAL
    eg = fromJust(EXGLOBAL)
    life = eg.egVarLifetime[v]
    eg.egVarUses[r] = VarUse(life.staticCtr)

def ex_unknown_expr(e):
    assert False, 'Unknown expr for expansion:\n' + repr(e)

def ex_expr(e):
    match(e,
        ("Int(_, _)", nop),
        ("Str(_, _)", nop),
        ("key('call', cons(f, sized(args)))", ex_call),
        ("lam==key('lambda', sized(args, cons(e, _)))", ex_lambda),
        ("key('tuplelit', sized(ts))", lambda ts: map_(ex_expr, ts)),
        ("key('listlit', sized(ls))", lambda ls: map_(ex_expr, ls)),
        ("m==key('match', cons(e, all(cs, c==key('case'))))", ex_match),
        ("key('attr', cons(s, cons(Ref(_, _), _)))", ex_expr),
        ("key('getctxt', cons(Ref(ctxt, _), _))", ex_getctxt),
        ("key('inctxt', cons(Ref(ctxt, _), cons(i, cons(f, _))))", ex_inctxt),
        ("r==Ref(v==key('var'), _)", ex_var),
        ("Ref(key('func' or 'ctor'), _)", nop),
        ("Ref(key('symbol', contains(key('type'))), _)", nop),
        ("otherwise", ex_unknown_expr))

def ex_defn(v, e):
    global EXGLOBAL, EXSCOPE
    EXGLOBAL.just.egVarLifetime[v] = VarLifetime(0)
    EXSCOPE.just.localVars[v] = None # What to store?
    ex_expr(e)

def ex_assign(v, e):
    ex_expr(e) # Must come first!
    global EXGLOBAL, EXSCOPE
    EXGLOBAL.just.egVarLifetime[v].staticCtr += 1
    destScope = fromJust(EXSCOPE)
    scope = EXSCOPE
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
    outgoingFlow = new_flow()
    for t, b in cs:
        ex_expr(t)
        flow = new_flow()
        add_outflows(incomingFlow, set([flow]))
        in_new_scope(lambda s: ex_body(b), flow, set([outgoingFlow]))
    eb = match(ss, ("contains(key('else', sized(body)))", Just),
                   ("_", Nothing))
    if isJust(eb):
        flow = new_flow()
        add_outflows(incomingFlow, set([flow]))
        in_new_scope(lambda s: ex_body(fromJust(eb)), flow, set([outgoingFlow]))
    activate_flow(outgoingFlow)

def ex_while(t, b):
    incomingFlow = cur_flow()
    outgoingFlow = new_flow()
    ex_expr(t)
    flow = new_flow()
    in_new_scope(lambda s: ex_body(b), flow, set([flow, outgoingFlow]))
    activate_flow(outgoingFlow)

def ex_assert(t, m):
    ex_expr(t)
    ex_expr(m)

def ex_func(f, args, b):
    global EXGLOBAL
    eg = fromJust(EXGLOBAL)
    for a in args:
        eg.egVarLifetime[a] = VarLifetime(0)

    def f_body(scope):
        scope.formalParams = args
        scope.funcScope = Just(scope)
        ex_body(b)
    in_new_scope(f_body, new_flow(), set())

def ex_return(e):
    if isJust(e):
        ex_expr(fromJust(e))
    cur_flow().returns = True
    # New flow is guaranteed dead. Blah. But OK for now.
    # (Avoiding dead code removal for now for debugability)
    activate_flow(new_flow())

def ex_stmt(s):
    match(s,
        ("key('exprstmt', cons(e, _))", ex_expr),
        ("key('defn', cons(v, cons(e, _)))", ex_defn),
        ("key('=', cons(Ref(v, _), cons(e, _)))", ex_assign),
        ("c==key('cond', ss and all(cs, key('case', cons(t, sized(b)))))",
            ex_cond),
        ("key('while', cons(t, contains(key('body', sized(b)))))", ex_while),
        ("key('assert', cons(t, cons(m, _)))", ex_assert),
        ("key('DT')", nop),
        ("key('CTXT')", nop),
        ("f==key('func', contains(key('args', sized(a))) "
                 "and contains(key('body', sized(b))))", ex_func),
        ("key('return', cons(e, _))", lambda e: ex_return(Just(e))),
        ("key('returnnothing')", lambda: ex_return(Nothing())))

def nop():
    pass

def ex_body(ss):
    map_(ex_stmt, ss)

def expand_ast(roots):
    if len(roots) == 0:
        return {}
    setup_ex_env(roots)
    global EXGLOBAL
    eg = EXGLOBAL.just
    for root in roots:
        eg.egCurTopLevelDecl = root
        ex_body(roots)
    return {globs.FuncAnnot: eg.egFuncAugs,
            globs.ExTypeAnnot: eg.egTypeAugs,
            globs.ExLambdaAnnot: eg.egLambdaRefs}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
