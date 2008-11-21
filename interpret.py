import ast
from atom import *
from base import *

Scope = DT('Scope', ('syms', {str: Atom}),
                    ('name', str),
                    ('prevScope', 'Scope'))

def run_module(module):
    builtinScope = Scope({}, '<builtins>', None)
    scope_stmts(module.roots, '<module-level>', builtinScope)

def expr_binary(op, subs, scope):
    if op == '%':
        return 'format'
    return op

def expr_builtin(op, subs, scope):
    return op

def expr_call(op, subs, scope):
    return match(subs, ('cons(f, contains(named("args", sized(args))))',
                        lambda f, args: '%s(%s)' % (eval_expr(f, scope),
                                        ', '.join(eval_exprs(args, scope)))))

def expr_cmp(op, subs, scope):
    return op

def expr_dictlit(op, subs, scope):
    pairs = match(subs, ('all(named("pair", cons(k, cons(v, _))))', identity))
    return '{%s}' % ', '.join(['%s : %s' % (eval_expr(k, scope),
                              eval_expr(v, scope)) for (k, v) in pairs])

def expr_genexpr(op, subs, scope):
    return match(subs, ('cons(e, cons(a, cons(l, sized(ps))))',
        lambda e, a, l, ps: '[%s for %s in %s%s]' % (
            eval_expr(e, scope), eval_expr(a, scope), eval_expr(l, scope),
            ''.join([' if ' + eval_expr(p, scope) for p in ps]))))

def expr_getattr(op, subs, scope):
    return '%s.%s' % (eval_expr(subs[0], scope), subs[1].strVal)

def expr_ident(op, subs, scope):
    return subs[0].strVal

def extract_argnames(args):
    return [match(a, ('named(nm)', identity)) for a in args]

def expr_lambda(op, subs, scope):
    return match(subs, ('sized(args, cons(code, _))',
                        lambda args, code: 'lambda %s: %s' % (
                            ', '.join(extract_argnames(args)),
                            eval_expr(code, scope))))

def expr_listlit(op, subs, scope):
    nargs = subs[0].intVal
    return '[%s]' % (', '.join(eval_exprs(subs[1:nargs+1], scope)),)

def expr_subscript(op, subs, scope):
    return '%s[%s]' % (eval_expr(subs[0], scope), eval_expr(subs[1], scope))

def expr_ternary(op, subs, scope):
    return '%s ? %s : %s' % (eval_expr(subs[0], scope),
                             eval_expr(subs[1], scope),
                             eval_expr(subs[2], scope))

def expr_tuplelit(op, subs, scope):
    nargs = subs[0].intVal
    if nargs == 0:
        return 'tuple()'
    elif nargs == 1:
        return '(%s,)' % (eval_expr(subs[1], scope),)
    return '(%s)' % (', '.join(eval_exprs(subs[1:nargs+1], scope)),)

expr_dispatch = {
        '+': expr_binary, '-': expr_binary, '%': expr_binary,
        'println': expr_builtin, 'slice': expr_builtin,
        'call': expr_call,
        '==': expr_cmp,
        'in': expr_cmp, 'not in': expr_cmp, 'is': expr_cmp, 'is not': expr_cmp,
        'dictlit': expr_dictlit,
        'genexpr': expr_genexpr,
        'getattr': expr_getattr,
        'ident': expr_ident,
        'lambda': expr_lambda,
        'listlit': expr_listlit,
        'subscript': expr_subscript,
        '?:': expr_ternary,
        'tuplelit': expr_tuplelit,
        'unpacktuple': expr_tuplelit,
    }

def eval_expr(expr, scope):
    nm = match(expr, ('named(nm)', identity), ('s', const(None)))
    if nm in expr_dispatch:
        return expr_dispatch[nm](nm, expr.subs, scope)
    elif nm is None:
        return match(expr, ('Str(s, _)', repr),
                           ('Int(i, _)', str),
                           ('ref', const('<unnamed>')))
    else:
        assert False, 'WTF is expr %s?' % (nm,)
        return '%s(%s)' % (nm, ', '.join(map(str, expr.subs)))

def eval_exprs(list, scope):
    return [eval_expr(sub, scope) for sub in list]

def stmt_assert(op, subs, scope):
    print 'assert %s, %s' % (eval_expr(subs[0], scope),
                             eval_expr(subs[1], scope))

def stmt_assign(op, subs, scope):
    print eval_expr(subs[0], scope), op, eval_expr(subs[1], scope)

def stmt_cond(op, subs, scope):
    kw = 'if'
    cases = match(subs, ('all(named("case", cons(test, sized(body))))',
                         identity))
    for (tst, body) in cases:
        print match(tst, ('named("else")', lambda: 'else:'),
                         ('t', lambda t: '%s %s:' % (kw, eval_expr(t, scope))))
        scope_stmts(body, scope.name + '.<cond>', scope)
        kw = 'elif'

def stmt_exprstmt(op, subs, scope):
    print eval_expr(subs[0], scope)

def stmt_for(op, subs, scope):
    print 'for %s in %s:' % match(subs, ('cons(a, cons(t, _))',
            lambda a, t: (eval_expr(a, scope), eval_expr(t, scope))))
    match(subs, ('cons(_, cons(_, contains(named("body", sized(stmts)))))',
                 lambda ss: scope_stmts(ss, scope.name + '.<for>', scope)))

def stmt_func(op, subs, scope):
    (name, args, body) = match(subs,
        ('contains(named("name", cons(Str(nm, _), _))) and \
          contains(named("args", sized(args))) and \
          contains(named("body", sized(body)))', lambda n,a,b: (n,a,b)))
    print 'def %s(%s):' % (name, ', '.join(extract_argnames(args)))
    scope_stmts(body, name, scope)

def stmt_return(op, subs, scope):
    print 'return', eval_expr(subs[0], scope)

def stmt_while(op, subs, scope):
    print 'while %s:' % (eval_expr(subs[0], scope),)
    match(subs, ('cons(_, contains(named("body", sized(stmts))))',
                 lambda ss: scope_stmts(ss, scope.name + '.<while>', scope)))

stmt_dispatch = {
        'assert': stmt_assert,
        '=': stmt_assign, '+=': stmt_assign, '-=': stmt_assign,
        'cond': stmt_cond,
        'exprstmt': stmt_exprstmt,
        'for': stmt_for,
        'func': stmt_func,
        'return': stmt_return,
        'while': stmt_while,
    }

def run_stmt(stmt, scope):
    nm = match(stmt, ('named(nm)', identity), ('s', const(None)))
    if nm in stmt_dispatch:
        stmt_dispatch[nm](nm, stmt.subs, scope)
    else:
        assert False, 'WTF is stmt %s?' % (nm,)

def scope_stmts(stmts, name, prev_scope):
    scope = Scope({}, name, prev_scope)
    for stmt in stmts:
        run_stmt(stmt, scope)

def scope_lookup(name, scope):
    while scope is not null:
        if name in scope.syms:
            return scope.syms[name]
        scope = scope.prevScope
    assert False, 'Symbol "%s" not defined' % (name,)

if __name__ == '__main__':
    run_module(ast.convert_file('interpret.py'))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
