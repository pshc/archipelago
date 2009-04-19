#!/usr/bin/env python
import ast
from atom import *
from base import *

ScopeInfo, FuncScope, CaseScope, WhileScope, ForScope = ADT('ScopeInfo',
        'FuncScope', ('calledFuncName', str), ('returnValue', Atom),
        'CaseScope',
        'WhileScope', ('loopCond', Atom), ('whileBody', [Atom]),
        'ForScope', ('forVar', Atom), ('loopList', []), ('forBody', [Atom]))

Scope = DT('Scope', ('syms', {Atom: Atom}),
                    ('scopeInfo', ScopeInfo),
                    ('stmts', [Atom]),
                    ('stmtsPos', int),
                    ('prevScope', 'Scope'))

Function = DT('Function', ('funcName', str),
                          ('argBindings', [Atom]),
                          ('funcStmts', [Atom]))

CTORS = {}
CTOR_FIELDS = []

EXIT_SCOPE = -2

def bi_print(s): print s

def run_module(module):
    builtins = {'+': lambda x, y: x + y, '-': lambda x, y: x - y,
                '*': lambda x, y: x * y, '%': lambda x, y: x % y,
                'negate': lambda x: -x,
                'True': True, 'False': False,
                '==': lambda x, y: x == y, '!=': lambda x, y: x != y,
                '<': lambda x, y: x < y, '>': lambda x, y: x > y,
                '<=': lambda x, y: x <= y, '>=': lambda x, y: x >= y,
                'is': lambda x, y: x is y, 'is not': lambda x, y: x is not y,
                'in': lambda x, y: x in y, 'not in': lambda x, y: x not in y,
                'slice': lambda l, d, u: l[d:u], 'len': lambda x: len(x),
                'print': bi_print,
                'object': make_record, 'getattr': getattr,
                'const': lambda x: lambda y: x, 'identity': lambda x: x,
                'tuple2': lambda x, y: (x, y),
                'tuple3': lambda x, y, z: (x, y, z),
                }
    biSyms = dict((boot_sym_names[nm], f) for nm, f in builtins.iteritems())
    builtinScope = new_scope(biSyms, None, [], None)
    run_scope(new_scope({}, '<top-level>', module.roots, builtinScope))

def expr_call(op, subs, scope):
    return match(subs, ('cons(f, sized(args))',
                        lambda f, args: call_func(eval_expr(f, scope),
                                                  eval_exprs(args, scope),
                                                  scope)))

def call_func(f, args, scope):
    bf = is_builtin_func(f)
    if bf is not None:
        return call_builtin_func(bf, args, scope)
    assert len(f.argBindings) == len(args), \
           'Bad arg count (%d) for calling %s' % (len(args), f.funcName)
    argvars = dict(zip(f.argBindings, args))
    scope = new_scope(argvars, FuncScope(f.funcName, None), f.funcStmts, scope)
    run_scope(scope)
    return scope.scopeInfo.returnValue

def expr_dictlit(op, subs, scope):
    ps = match(subs, ('all(ps, key("pair", cons(k, cons(v, _))))', identity))
    return dict([(eval_expr(k, scope), eval_expr(v, scope)) for (k, v) in ps])

def expr_genexpr(op, subs, scope):
    (e, a, l, ps) = match(subs, ('cons(e, cons(a, cons(l, sized(ps))))',
                                 tuple4))
    results = []
    for item in eval_expr(l, scope):
        do_assign(a, item, scope)
        ok = True
        for cond in ps:
            if not eval_expr(cond, scope):
                ok = False
                break
        if ok:
            results.append(eval_expr(e, scope))
    return results

def expr_getattr(op, subs, scope):
    return getattr(eval_expr(subs[0], scope), getident(subs[1]))

def expr_lambda(op, subs, scope):
    (args, expr) = match(subs, ('sized(every(args, arg==key("var")), \
                                       cons(expr, _))', tuple2))
    return Function(None, args, [symref('return', [expr])])

def expr_listlit(op, subs, scope):
    return eval_exprs(match(subs, ('sized(items)', identity)), scope)

def expr_subscript(op, subs, scope):
    return eval_expr(subs[0], scope)[eval_expr(subs[1], scope)]

def expr_ternary(op, subs, scope):
    return eval_expr(subs[1], scope) if eval_expr(subs[0], scope) \
                                     else eval_expr(subs[2], scope)

def expr_tuplelit(op, subs, scope):
    return tuple(eval_exprs(match(subs, ('sized(items)', identity)), scope))

def match_or(ps, e):
    for p in ps:
        r = pat_match(p, e)
        if r is not None:
            return r
    return None

def match_and(ps, e):
    rs = []
    for p in ps:
        r = pat_match(p, e)
        if r is None:
            return None
        rs += r
    return rs

def match_capture(v, pat, e):
    r = pat_match(pat, e)
    if r is None:
        return None
    r.append((v, e))
    return r

def match_ctor(ctor, args, e):
    nm = getident(ctor)
    if CTORS[nm] != e._ix:
        return None
    fs = CTOR_FIELDS[e._ix]
    rs = []
    for f, a in zip(fs, args):
        r = pat_match(a, getattr(e, getname(f)))
        if r is None:
            return None
        rs += r
    return rs

def match_contains(p, es):
    for e in es:
        r = pat_match(p, e)
        if r is not None:
            return r
    return None

def match_cons(hp, tp, e):
    h, t = match(e, ('cons(h, t)', tuple2))
    hr = pat_match(hp, e)
    if hr is None:
        return None
    tr = pat_match(tp, e)
    return None if tr is None else hr + tr

def match_all(v, p, es):
    rs = []
    all_singular = True
    for e in es:
        r = pat_match(p, e)
        if r is None:
            continue
        if len(r) != 1:
            all_singular = False
        rs.append([val for var, val in r])
    return [(v, [r[0] for r in rs] if all_singular else rs)]

def match_every(v, p, es):
    rs = []
    all_singular = True
    for e in es:
        r = pat_match(p, e)
        if r is None:
            return None
        if len(r) != 1:
            all_singular = False
        rs.append([val for var, val in r])
    return [(v, [r[0] for r in rs] if all_singular else rs)]

def match_sized2(hp, tp, e):
    h, t = match(e, ('sized(h, t)', tuple2))
    hr = pat_match(hp, h)
    if hr is None:
        return None
    tr = pat_match(tp, t)
    return None if tr is None else hr + tr

def match_key2(kp, sp, e):
    k, s = match(e, ('key(k, s)', tuple2))
    kr = pat_match(kp, k)
    if kr is None:
        return None
    sr = pat_match(sp, s)
    return None if sr is None else kr + sr

def match_named2(np, sp, e):
    n, s = match(e, ('named(n, s)', tuple2))
    nr = pat_match(np, n) # oshi
    if nr is None:
        return None
    sr = pat_match(sp, s)
    return None if sr is None else nr + sr

def pat_match(pat, e):
    return match(pat,
            ('Int(i, _)', lambda i: [] if i == e else None),
            ('Str(s, _)', lambda s: [] if s == e else None),
            ('v==key("var", _)', lambda v: [(v, e)]),
            ('key("wildcard", _)', lambda: []),
            ('key("ctor", cons(c, sized(args)))',
                lambda c, args: match_ctor(c, args, e)),
            ('key("or", sized(ps))', lambda ps: match_or(ps, e)),
            ('key("and", sized(ps))', lambda ps: match_and(ps, e)),
            ('key("capture", cons(v, cons(p, _)))',
                lambda v, p: match_capture(v, p, e)),
            ('key("sized1", cons(p, _))',
                lambda p: match(e, ('sized(s)', lambda s: try_match(p, s)))),
            ('key("sized2", cons(p, cons(q, _)))',
                lambda p, q: match_sized2(p, q, e)),
            ('key("key1", cons(p, _))',
                lambda p: match(e, ('key(k)', lambda k: try_match(p, k)))),
            ('key("key2", cons(p, cons(q, _)))',
                lambda p, q: match_key2(p, q, e)),
            ('key("named1", cons(p, _))',
                lambda p: match(e, ('named(n)', lambda n: try_match(p, n)))),
            ('key("named2", cons(p, cons(q, _)))',
                lambda p, q: match_named2(p, q, e)),
            ('key("contains1", cons(p, _))', lambda p: match_contains(p, e)),
            ('key("cons2", cons(h, cons(t, _)))',
                lambda h, t: match_cons(h, t, e)),
            ('key("all2", cons(v, cons(p, _)))',
                lambda v, p: match_all(v, p, e)),
            ('key("every2", cons(v, cons(p, _)))',
                lambda v, p: match_every(v, p, e)),
            )

def expr_match(op, subs, scope):
    e, cs = match(subs, ('cons(e, all(cs, key("case", cons(p, cons(f, _)))))',
                         tuple2))
    expr = eval_expr(e, scope)
    for pat, f in cs:
        bs = pat_match(pat, expr)
        if bs is not None:
            return eval_expr(f, new_scope(dict(bs), CaseScope(), [], scope))
    assert False, "Match failed"

expr_dispatch = {
        'call': expr_call,
        'dictlit': expr_dictlit,
        'genexpr': expr_genexpr,
        'attr': expr_getattr,
        'lambda': expr_lambda,
        'listlit': expr_listlit,
        'subscript': expr_subscript,
        '?:': expr_ternary,
        'tuplelit': expr_tuplelit,
        'match': expr_match,
    }

def eval_expr(expr, scope):
    nm = match(expr, ('key(nm)', identity), ('s', const(None)))
    if nm in expr_dispatch:
        return expr_dispatch[nm](nm, expr.subs, scope)
    #elif nm is not None:
    #    return scope_lookup(expr, scope)
    #assert nm is None, "Unknown expr key '%s'" % (nm,)
    return match(expr, ('Str(s, _)', identity),
                       ('Int(i, _)', identity),
                       ('Ref(r, _, _)', lambda r: scope_lookup(r, scope)))

def eval_exprs(list, scope):
    return [eval_expr(sub, scope) for sub in list]

ADTCtors = DT('ADTCtors', ('ctorList', [str]))

def stmt_ADT(stmt, scope):
    (name, cs) = match(stmt, ('named(name, all(cs, c==key("ctor")))', tuple2))
    scope.syms[stmt] = ADTCtors(cs)
    for ctor in cs:
        scope = stmt_DT(ctor, scope)
    return scope

def stmt_assert(stmt, scope):
    assert eval_expr(stmt.subs[0], scope), eval_expr(stmt.subs[1], scope)
    return scope

def list_scope(scope):
    additional = ''
    p = scope.prevScope
    if p is not None and p.scopeInfo is not None:
        additional = '\nUnder scope %s:\n%s' % (p.scopeInfo, list_scope(p))
    return '\n'.join('\t%s\t%s' % (getname(k), v)
                                   for k, v in scope.syms.iteritems()) \
           + additional

# Returns the scope which nm should be assigned into
def dest_scope(ref, scope):
    cur = scope
    while cur is not None:
        if ref in cur.syms:
            return cur
        cur = cur.prevScope
    assert False, '"%s" not defined in scope %s:\n%s\n' % (
                  getname(ref), scope.scopeInfo, list_scope(scope))

def assign_new(var, val, scope):
    scope.syms[var] = val

def assign_var(var, val, scope):
    dest = dest_scope(var, scope).syms
    dest[var] = val

def assign_tuple(bs, val, scope):
    for b, v in zip(bs, val):
        if match(b, ('key("var")', lambda: True), ('_', lambda: False)):
            assign_new(b, v, scope)
        else:
            assign_var(b, v, scope)

def assign_sub(c, sub, val, scope):
    dest = dest_scope(c, scope).syms[c]
    dest[eval_expr(sub, scope)] = val

def assign_attr(obj, attr, val, scope):
    dest = dest_scope(obj, scope).syms[obj]
    setattr(dest, getident(attr), val)

def do_assign(dest, val, scope):
    match(dest, ('n==key("var")',
                    lambda n: assign_new(n, val, scope)),
                ('Ref(v==key("var"), _, _)',
                    lambda v: assign_var(v, val, scope)),
                ('key("tuplelit", sized(bits))',
                    lambda bs: assign_tuple(bs, val, scope)),
                ('key("subscript", cons(Ref(d, _, _), cons (ix, _)))',
                    lambda d, ix: assign_sub(d, ix, val, scope)),
                ('key("attr", cons(Ref(o, _, _), cons(a, _)))',
                    lambda o, a: assign_attr(o, a, val, scope)))
    return scope

def stmt_assign(stmt, scope):
    left, e = match(stmt, ('key("=", cons(left, cons(e, _)))', tuple2))
    do_assign(left, eval_expr(e, scope), scope)
    return scope

def enclosing_loop(scope):
    return match(scope.scopeInfo, ('ForScope(_, _, _)', lambda: scope),
                                  ('WhileScope(_, _, _)', lambda: scope),
                                  ('CaseScope()',
                                      lambda: enclosing_loop(scope.prevScope)),
                                  ('_', lambda: None))

def break_for(for_scope):
    for_scope.loopList = []

def break_while(while_scope):
    while_scope.loopCond = False

def stmt_break(stmt, scope):
    scope = enclosing_loop(scope)
    match(scope.scopeInfo, ('f==ForScope(_, _, _)', break_for),
                           ('w==WhileScope(_, _, _)', break_while))
    scope.stmtsPos = EXIT_SCOPE
    return scope

def stmt_cond(stmt, scope):
    cases = match(stmt.subs, ('all(cs, key("case", cons(test, sized(body))))',
                              identity))
    for (tst, body) in cases:
        if match(tst, ('key("else")', lambda: True),
                      ('t', lambda t: eval_expr(t, scope))):
            return new_scope({}, CaseScope(), body, scope)
    return scope

def stmt_continue(stmt, scope):
    assert enclosing_loop(scope) is not None, "Bad continue"
    scope.stmtsPos = EXIT_SCOPE
    return scope

def stmt_DT(stmt, scope):
    # Getattr is already done for us; all we need is the constructor
    name, fs = match(stmt, ('named(nm, all(fs, f==key("field", _)))', tuple2))
    ix = len(CTOR_FIELDS)
    CTORS[name] = ix
    CTOR_FIELDS.append(fs) # Yes, appending a list
    obj = symref('var', [symname('obj')])
    objref = Ref(obj, None, [])
    stmts = [symref('=', [obj, symcall('object', [])]),
             symref('=', [symref('attr', [objref, symref('_ix', [])]),
                          Int(ix, [])])]
    args = []
    for f in fs:
        arg = symref('var', [symname(getident(f))])
        args.append(arg)
        stmts.append(symref('=', [symref('attr', [objref, Ref(f, None, [])]),
                                  Ref(arg, None, [])]))
    stmts.append(symref('return', [objref]))
    scope.syms[stmt] = Function(name, args, stmts)
    return scope

def stmt_exprstmt(stmt, scope):
    eval_expr(stmt.subs[0], scope)
    return scope

def stmt_for(stmt, scope):
    a, ls, body = match(stmt.subs,
        ('cons(a, cons(ls, contains(key("body", sized(body)))))', tuple3))
    items = eval_expr(ls, scope)
    for_scope = new_scope({}, ForScope(a, items, body), body, scope)
    for_scope.stmtsPos = EXIT_SCOPE
    return for_scope

def stmt_func(stmt, scope):
    scope.syms[stmt] = match(stmt,
        ('named(nm) and key("func", \
          contains(key("args", sized(every(args, arg==key("var"))))) and \
          contains(key("body", sized(body))))', Function))
    return scope

def stmt_return(stmt, scope):
    this_frame = scope
    while True:
        assert this_frame is not None, 'Cannot return from root scope'
        if match(this_frame.scopeInfo, ('FuncScope(_, _)', lambda: True),
                                       ('_', lambda: False)):
            break
        this_frame = this_frame.prevScope
    this_frame.scopeInfo.returnValue = eval_expr(stmt.subs[0], scope)
    this_frame.stmtsPos = EXIT_SCOPE
    return this_frame

def stmt_while(stmt, scope):
    test, body = match(stmt.subs, ('cons(t, contains(key("body", sized(b))))',
                                   tuple2))
    if not eval_expr(test, scope):
        return scope
    return new_scope({}, WhileScope(test, body), body, scope)

stmt_dispatch = {
        'ADT': stmt_ADT,
        'assert': stmt_assert,
        '=': stmt_assign, '+=': stmt_assign, '-=': stmt_assign,
        'break': stmt_break,
        'cond': stmt_cond,
        'continue': stmt_continue,
        'DT': stmt_DT,
        'exprstmt': stmt_exprstmt,
        'for': stmt_for,
        'func': stmt_func,
        'return': stmt_return,
        'while': stmt_while,
    }

def loop_while(cond, scope):
    if eval_expr(cond, scope):
        scope.stmtsPos = 0
        return True
    return False

def loop_for(var, list, scope):
    if len(list) > 0:
        do_assign(var, list.pop(0), scope)
        scope.stmtsPos = 0
        return True
    return False

def run_scope(scope):
    orig_scope = scope
    while scope is not None:
        while scope.stmtsPos >= 0 and scope.stmtsPos < len(scope.stmts):
            scope.stmtsPos += 1
            scope = run_stmt(scope.stmts[scope.stmtsPos - 1], scope)
        if scope is orig_scope:
            break
        if not match(scope.scopeInfo,
                ('WhileScope(c, _)', lambda c: loop_while(c, scope)),
                ('ForScope(v, l, _)', lambda v, l: loop_for(v, l, scope)),
                ('CaseScope()', lambda: False)):
            scope = scope.prevScope


def run_stmt(stmt, scope):
    nm = match(stmt, ('key(nm)', identity), ('_', lambda: None))
    assert nm in stmt_dispatch, 'Unknown statement %s' % (nm,)
    return stmt_dispatch[nm](stmt, scope)

def new_scope(syms, info, scopeStmts, prev_scope):
    return Scope(syms, info, scopeStmts, 0, prev_scope)

def scope_lookup(ref, scope):
    return dest_scope(ref, scope).syms[ref]

if __name__ == '__main__':
    import sys
    filename = sys.argv[1] if len(sys.argv) > 1 else 'interpret.py'
    module = ast.convert_file(filename)
    f = open('hello', 'w')
    for r in module.roots:
        f.write(repr(r))
    del f, r, filename
    print 'Converted'
    serialize_module(module)
    run_module(module)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
