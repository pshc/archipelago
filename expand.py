#!/usr/bin/env python2
from base import *
from atom import *
import globs

ExScope = DT('ExScope', ('freeParams', {Atom: Atom}),
                        ('localVars', {Atom: Atom}),
                        ('closedVars', {Atom: Atom}),
                        ('prevScope', 'ExScope'))

EXSCOPE = Nothing()

ExGlobal = DT('ExGlobal', ('egCurTopLevelDecl', Atom),
                          ('egFuncAugs', {Atom: Atom}),
                          ('egRefReplacements', {Atom: Atom}))

EXGLOBAL = Nothing()

def setup_ex_env(roots):
    global EXSCOPE
    EXSCOPE = Nothing()
    global EXGLOBAL
    EXGLOBAL = Just(ExGlobal(roots[0], {}, {}))

def ex_call(f, args):
    ex_expr(f)
    map_(ex_expr, args)

def ex_lambda(lam, args, e):
    # Closure time
    # Gotta rebind them args?
    nm = symname('lambda_func')
    fargs = [int_len(args)] + [ref_(a) for a in args] # XXX
    fbody = [int_(1), symref('return', [ref_(e)])]
    f = symref('func', [nm, symref('args', fargs), symref('body', fbody)])

    global EXGLOBAL
    eg = fromJust(EXGLOBAL)
    key = eg.egCurTopLevelDecl

    if key not in eg.egFuncAugs:
        eg.egFuncAugs[key] = []
    eg.egFuncAugs[key].append(f)

    ex_expr(e)

def ex_match_case(c):
    pass

def ex_match(m, e, cs):
    ex_expr(e)
    for c in cs:
        ex_match_case(c)

def ex_defref(a):
    # Check for closed-over func vars
    pass

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
        ("Ref(a, _)", ex_defref)) # XXX: catch-all still sucks

def ex_cond(ss, cs):
    for t, b in cs:
        ex_expr(t)
        ex_body(b)
    match(ss, ("contains(key('else', sized(body)))", ex_body),
              ("_", lambda: None))

def ex_while(t, b):
    ex_expr(t)
    ex_body(b)

def ex_assert(t, m):
    ex_expr(t)
    ex_expr(m)

def ex_func(f, a, b):
    global EXSCOPE

    EXSCOPE = ExScope({}, {}, {}, EXSCOPE)
    ex_body(b)
    EXSCOPE = EXSCOPE.prevScope

def ex_stmt(s):
    match(s,
        ("key('exprstmt', cons(e, _))", ex_expr),
        ("key('defn', cons(_, cons(e, _)))", ex_expr),
        ("key('=', cons(Ref(_, _), cons(e, _)))", ex_expr),
        ("key('cond', ss and all(cs, key('case', cons(t, sized(b)))))",
            ex_cond),
        ("key('while', cons(t, contains(key('body', sized(b)))))", ex_while),
        ("key('assert', cons(t, cons(m, _)))", ex_assert),
        ("key('DT')", nop),
        ("f==key('func', contains(key('args', sized(a))) "
                 "and contains(key('body', sized(b))))", ex_func),
        ("key('return', cons(e, _))", ex_expr),
        ("key('returnnothing')", nop))

def nop():
    pass

def ex_body(ss):
    map_(ex_stmt, ss)

def expand_ast(roots):
    if len(roots) == 0:
        return {}
    setup_ex_env(roots)
    global EXGLOBAL
    for root in roots:
        EXGLOBAL.just.egCurTopLevelDecl = root
        ex_body(roots)
    return {globs.FuncAnnot: EXGLOBAL.just.egFuncAugs}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
