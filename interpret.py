#!/usr/bin/env python
import ast
from atom import *
from base import *

ScopeInfo, FuncScope, WhileScope, ForScope = ADT('ScopeInfo',
        'FuncScope', ('name', str), ('returnValue', Atom),
        'WhileScope', ('cond', Atom), ('body', [Atom]),
        'ForScope', ('var', Atom), ('loopList', []), ('body', [Atom]))

Scope = DT('Scope', ('syms', {str: Atom}),
                    ('scopeInfo', ScopeInfo),
                    ('stmts', [Atom]),
                    ('prevScope', 'Scope'))

Function = DT('Function', ('name', str),
                          ('argnames', [str]),
                          ('stmts', [Atom]))

def bi_print(s): print s

def run_module(module):
    builtins = {'+': lambda x, y: x + y, '-': lambda x, y: x - y,
                '%': lambda x, y: x % y,
                '==': lambda x, y: x == y, '!=': lambda x, y: x != y,
                '<': lambda x, y: x < y, '>': lambda x, y: x > y,
                '<=': lambda x, y: x <= y, '>=': lambda x, y: x >= y,
                'is': lambda x, y: x is y, 'is not': lambda x, y: x is not y,
                'in': lambda x, y: x in y, 'not in': lambda x, y: x not in y,
                'slice': lambda l, d, u: l[d:u], 'print': bi_print,
                'object': make_record,
                }
    builtinScope = new_scope(builtins, None, [], None)
    run_scope(new_scope({}, '<top-level>', module.roots[:], builtinScope))

def expr_call(op, subs, scope):
    return match(subs, ('cons(f, contains(key("args", sized(args))))',
                        lambda f, args: call_func(eval_expr(f, scope),
                                                  eval_exprs(args, scope),
                                                  scope)))

def call_func(f, args, sc):
    return match(f, ('Function(_, _, _)', lambda: call_func_obj(f, args, sc)),
                    ('func', lambda func: func(*args)))

def call_func_obj(f, args, scope):
    assert len(f.argnames) == len(args), \
           'Bad arg count (%d) for calling %s' % (len(args), f.name)
    argvars = dict(zip(f.argnames, args))
    scope = new_scope(argvars, FuncScope(f.name, None), f.stmts, scope)
    run_scope(scope)
    return scope.scopeInfo.returnValue

def expr_dictlit(op, subs, scope):
    pairs = match(subs, ('all(key("pair", cons(k, cons(v, _))))', identity))
    return dict([(eval_expr(k, scope), eval_expr(v, scope))
                 for (k, v) in pairs])

def expr_genexpr(op, subs, scope):
    (e, a, l, ps) = match(subs, ('cons(e, cons(a, cons(l, sized(ps))))',
                                 tuple4))
    results = []
    for item in eval_expr(l, scope):
        do_assign(a, item, scope)
        # TODO: Proper fold or something
        ok = True
        for cond in ps:
            if not eval_expr(cond, scope):
                ok = False
                break
        if ok:
            results.append(eval_expr(e, scope))
    return results

def expr_getattr(op, subs, scope):
    return getattr(eval_expr(subs[0], scope), subs[1].strVal)

def expr_ident(op, subs, scope):
    return scope_lookup(subs[0].strVal, scope)

def extract_argnames(args):
    return [match(a, ('key("name", cons(Str(nm), _))', identity))
            for a in args]

def expr_lambda(op, subs, scope):
    (args, expr) = match(subs, ('sized(args, cons(expr, _))', tuple2))
    return Function(None, extract_argnames(args), symref('return', [expr]))

def expr_listlit(op, subs, scope):
    return eval_exprs(match(subs, ('sized(items)', identity)), scope)

def expr_subscript(op, subs, scope):
    return eval_expr(subs[0], scope)[eval_expr(subs[1], scope)]

def expr_ternary(op, subs, scope):
    return eval_expr(subs[1], scope) if eval_expr(subs[0], scope) \
                                     else eval_expr(subs[2], scope)

def expr_tuplelit(op, subs, scope):
    return tuple(eval_exprs(match(subs, ('sized(items)', identity)), scope))

expr_dispatch = {
        'call': expr_call,
        'dictlit': expr_dictlit,
        'genexpr': expr_genexpr,
        'attr': expr_getattr,
        'ident': expr_ident,
        'lambda': expr_lambda,
        'listlit': expr_listlit,
        'subscript': expr_subscript,
        '?:': expr_ternary,
        'tuplelit': expr_tuplelit,
        'unpacktuple': expr_tuplelit,
    }

def eval_expr(expr, scope):
    nm = match(expr, ('key(nm)', identity), ('s', const(None)))
    if nm in expr_dispatch:
        return expr_dispatch[nm](nm, expr.subs, scope)
    elif nm is None:
        return match(expr, ('Str(s, _)', identity),
                           ('Int(i, _)', identity),
                           ('ref', lambda r: TODO_DUNNO_LOL))
    else:
        return scope_lookup(nm, scope)

def eval_exprs(list, scope):
    return [eval_expr(sub, scope) for sub in list]

def stmt_ADT(op, subs, scope):
    return scope

def stmt_assert(op, subs, scope):
    assert eval_expr(subs[0], scope), eval_expr(subs[1], scope)
    return scope

# Returns the scope which nm should be assigned into
def dest_scope(nm, scope):
    cur_scope = scope
    while cur_scope is not None:
        if nm in cur_scope.syms:
            return cur_scope
        cur_scope = cur_scope.prevScope
    return scope

def assign_nm(nm, val, scope):
    dest = dest_scope(nm, scope).syms
    dest[nm] = val

def assign_sub(container, sub, val, scope):
    nm = getident(container)
    dest = dest_scope(nm, scope).syms[nm]
    dest[eval_expr(sub, scope)] = val

def assign_attr(obj, attr, val, scope):
    nm = getident(obj)
    dest = dest_scope(nm, scope).syms[nm]
    setattr(dest, getident(attr), val)

def do_assign(dest, val, scope):
    match(dest, ('key("ident", cons(Str(nm), _))',
                    lambda nm: assign_nm(nm, val, scope)),
                ('key("subscript", cons(d, cons (ix, _)))',
                    lambda d, ix: assign_sub(d, ix, val, scope)),
                ('key("attr", cons(o, cons(a, _)))',
                    lambda o, a: assign_attr(o, a, val, scope)))
    return scope

def stmt_assign(op, subs, scope):
    if op == '=':
        do_assign(subs[0], eval_expr(subs[1], scope), scope)
        return scope
    assert False

def break_for(for_scope):
    for_scope.loopList = []

def break_while(while_scope):
    while_scope.cond = False

def stmt_break(op, subs, scope):
    match(scope.scopeInfo, ('f==ForScope(_, _, _)', break_for),
                           ('w==WhileScope(_, _, _)', break_while))
    scope.stmts = []
    return scope

def stmt_cond(op, subs, scope):
    cases = match(subs, ('all(key("case", cons(test, sized(body))))',
                         identity))
    for (tst, body) in cases:
        if match(tst, ('key("else")', lambda: True),
                      ('t', lambda t: eval_expr(t, scope))):
            scope.stmts = body + scope.stmts
            break
    return scope

def stmt_continue(op, subs, scope):
    assert match(scope.scopeInfo, ('WhileScope(_, _)', lambda: True),
                                  ('ForScope(_, _, _)', lambda: True),
                                  ('otherwise', lambda: False)), "Bad continue"
    scope.stmts = []
    return scope

def stmt_DT(op, subs, scope):
    # Getattr is already done for us; all we need is the constructor
    (name, fs) = match(subs, ('contains(key("name", cons(Str(nm, _), _))) and\
                               all(key("field", _) and named(f))', tuple2))
    fs = [f[0] for f in fs] # Hmmm...
    scope.syms[name] = Function(name, fs,
            [symref('=', [symident('obj', []), symcall('object', [])])] +
            [symref('=', [symref('attr', [symident('obj', []),
                                          symident(f, [])]),
                          symident(f, [])])
             for f in fs] +
            [symref('return', [symident('obj', [])])])
    return scope

def stmt_exprstmt(op, subs, scope):
    eval_expr(subs[0], scope)
    return scope

def stmt_for(op, subs, scope):
    (a, ls, body) = match(subs,
        ('cons(a, cons(ls, contains(key("body", sized(body)))))', tuple3))
    items = eval_expr(ls, scope)
    if not len(items):
        return scope
    first = items.pop(0)
    for_scope = new_scope({}, ForScope(a, items, body), body, scope)
    do_assign(a, first, for_scope)
    return for_scope

def stmt_func(op, subs, scope):
    (name, args, body) = match(subs,
        ('contains(key("name", cons(Str(nm, _), _))) and \
          contains(key("args", sized(args))) and \
          contains(key("body", sized(body)))', tuple3))
    scope.syms[name] = Function(name, extract_argnames(args), body)
    return scope

def stmt_return(op, subs, scope):
    this_frame = scope
    while True:
        assert this_frame is not None, 'Cannot return from root scope'
        if match(this_frame.scopeInfo, ('FuncScope(_, _)', lambda: True),
                                       ('_', lambda: False)):
            break
        this_frame = this_frame.prevScope
    this_frame.scopeInfo.returnValue = eval_expr(subs[0], scope)
    this_frame.stmts = []
    return this_frame

def stmt_while(op, subs, scope):
    (test, body) = match(subs, ('cons(t, contains(key("body", sized(b))))',
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

def loop_while(cond, body, scope):
    if eval_expr(cond, scope):
        scope.stmts = body[:]
        return True
    return False

def loop_for(var, list, body, scope):
    if len(list) > 0:
        do_assign(var, list.pop(0), scope)
        scope.stmts = body[:]
        return True
    return False

def run_scope(scope):
    orig_scope = scope
    while scope is not None:
        while len(scope.stmts) > 0:
            scope = run_stmt(scope.stmts.pop(0), scope)
        if scope is orig_scope:
            break
        if not match(scope.scopeInfo,
                ('WhileScope(c,b)', lambda c, b: loop_while(c, b, scope)),
                ('ForScope(v,l,b)', lambda v, l, b: loop_for(v, l, b, scope))):
            scope = scope.prevScope


def run_stmt(stmt, scope):
    nm = match(stmt, ('key(nm)', identity), ('s', const(None)))
    if nm in stmt_dispatch:
        return stmt_dispatch[nm](nm, stmt.subs, scope)
    else:
        assert False, 'WTF is stmt %s?' % (nm,)

def new_scope(syms, info, stmts, prev_scope):
    return Scope(syms, info, stmts[:], prev_scope)

def scope_lookup(name, scope):
    cur = scope
    while cur is not None:
        if name in cur.syms:
            return cur.syms[name]
        cur = cur.prevScope
    assert False, 'Symbol "%s" not defined in scope %s:\n%s\n' % (name,
                  scope.scopeInfo,
                  '\n'.join('\t%s\t%s' % i for i in scope.syms.iteritems()))

if __name__ == '__main__':
    import sys
    filename = sys.argv[1] if len(sys.argv) > 1 else 'interpret.py'
    module = ast.convert_file(filename)
    open('hello', 'w').write(str(module.roots))
    print 'Converted'
    run_module(module)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
