#!/usr/bin/env python
import ast
from atom import *
from base import *
from builtins import builtins, ArrayAtom
import types

ScopeInfo, FuncScope, CaseScope, WhileScope, ForScope = ADT('ScopeInfo',
        'FuncScope', ('calledFuncName', str), ('returnValue', Atom),
        'CaseScope',
        'WhileScope', ('loopCond', Atom), ('whileBody', [Atom]),
        'ForScope', ('forVar', Atom), ('loopList', []), ('loopPos', int),
                    ('forBody', [Atom]))

Scope = DT('Scope', ('syms', {Atom: Atom}),
                    ('scopeInfo', ScopeInfo),
                    ('stmts', [Atom]),
                    ('stmtsPos', int),
                    ('prevScope', 'Scope'))

Function = DT('Function', ('funcName', str),
                          ('argBindings', [Atom]),
                          ('funcStmts', [Atom]))

CTORS = {'Int': 0, 'Str': 1, 'Ref': 2}
CTOR_FIELDS = [('intVal', 'subs'), ('strVal', 'subs'),
               ('refAtom', 'refMod', 'subs')]

SCOPE_END = -2
SCOPE_BREAK = -3

MethodDescriptorType = type(dict.keys)

def is_builtin_func(r):
    if isinstance(r, (types.FunctionType, types.BuiltinFunctionType,
            types.TypeType, MethodDescriptorType)):
        return r
    return builtins.get(match(r, ('key(nm)', identity),
                                 ('_', lambda: None)))

def run_module(module):
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
        return apply(bf, args)
    assert len(f.argBindings) == len(args), \
           'Bad arg count (%d) for calling %s' % (len(args), f.funcName)
    argvars = dict(zip(f.argBindings, args))
    scope = new_scope(argvars, FuncScope(f.funcName, None), f.funcStmts, scope)
    run_scope(scope)
    return scope.scopeInfo.returnValue

def expr_dictlit(op, subs, scope):
    ps = match(subs, ('all(ps, key("pair", cons(k, cons(v, _))))', identity))
    return dict([(eval_expr(k, scope), eval_expr(v, scope)) for (k, v) in ps])

EQUALS, PLUS_EQUALS, MINUS_EQUALS = 1, 2, 3

def assign_new(var, op, val, scope):
    assert op == EQUALS
    scope.syms[var] = val

def assign_var(var, op, val, scope):
    dest = dest_scope(var, scope).syms
    if op == EQUALS:
        dest[var] = val
    elif op == PLUS_EQUALS:
        dest[var] += val
    elif op == MINUS_EQUALS:
        dest[var] -= val
    else:
        assert False

def assign_tuple(bs, op, val, scope):
    assert op == EQUALS
    for b, v in zip(bs, val):
        match(b, ('key("var")',   lambda: assign_new(b, op, v, scope)),
                 ('Ref(r, _, _)', lambda r: assign_var(r, op, v, scope)))

def assign_sub(c, sub, op, val, scope):
    dest = dest_scope(c, scope).syms[c]
    s = eval_expr(sub, scope)
    if op == EQUALS:
        dest[s] = val
    elif op == PLUS_EQUALS:
        dest[s] += val
    elif op == MINUS_EQUALS:
        dest[s] -= val
    else:
        assert False

def assign_attr(obj, attr, op, val, scope):
    dest = dest_scope(obj, scope).syms[obj]
    f = getident(attr)
    if f == 'field':
        nm = getname(attr)
    elif f == 'symbol':
        nm = getname(attr)
        assert nm in ArrayAtom.__slots__, 'Unknown builtin attr: %s' % (nm,)
    else:
        assert False, 'Must getattr on a field, not %s' % (f,)
    if op == EQUALS:
        setattr(dest, nm, val)
        return
    old = getattr(dest, nm)
    if op == PLUS_EQUALS:
        setattr(dest, nm, old + val)
    elif op == MINUS_EQUALS:
        setattr(dest, nm, old - val)
    else:
        assert False

def do_assign(dest, op, val, scope):
    match(dest, ('n==key("var")',
                    lambda n: assign_new(n, op, val, scope)),
                ('Ref(v==key("var"), _, _)',
                    lambda v: assign_var(v, op, val, scope)),
                ('key("tuplelit", sized(bits))',
                    lambda bs: assign_tuple(bs, op, val, scope)),
                ('key("subscript", cons(Ref(d, _, _), cons (ix, _)))',
                    lambda d, ix: assign_sub(d, ix, op, val, scope)),
                ('key("attr", cons(Ref(o, _, _), cons(Ref(a, _, _), _)))',
                    lambda o, a: assign_attr(o, a, op, val, scope)))
    return scope

def expr_genexpr(op, subs, scope):
    (e, a, l, ps) = match(subs, ('cons(e, cons(a, cons(l, sized(ps))))',
                                 tuple4))
    results = []
    for item in eval_expr(l, scope):
        do_assign(a, EQUALS, item, scope)
        ok = True
        for cond in ps:
            if not eval_expr(cond, scope):
                ok = False
                break
        if ok:
            results.append(eval_expr(e, scope))
    return results

def expr_getattr(op, subs, scope):
    attr = match(subs[1], ('Ref(f, _, _)', identity))
    f = getident(attr)
    if f == 'field':
        nm = getname(attr)
    elif f == 'symbol':
        nm = getname(attr)
        assert nm in ArrayAtom.__slots__, 'Unknown builtin attr: %s' % (nm,)
    else:
        assert False, 'getattr on something other than a field: %s' % (f,)
    return getattr(eval_expr(subs[0], scope), nm)

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

def is_wildcard_match(ast):
    return isinstance(ast, Name) and ast.name == '_'

def match_array_atom(nm, astargs, e):
    (mod, n) = e
    atom = mod.modAtoms[n]
    ix = atom._ix
    assert 0 <= ix < 3, "Bad ArrayAtom index: %d" % ix
    subix = 1
    if ix == 0 and nm == 'Int':
        args = pat_match(astargs[0], atom.val)
    elif ix == 1 and nm == 'Str':
        args = pat_match(astargs[0], atom.ptr)
    elif ix == 2 and nm == 'Ref':
        args = pat_match(astargs[0], atom.ptr.modAtoms[atom.val])
        if args is None: return None
        args2 = pat_match(astargs[1], atom.ptr)
        if args2 is None: return None
        args += args2
        subix = 2
    else:
        return None
    # Walk subatoms
    ss = []
    if atom.hassubs:
        sx = n + 1
        while sx:
            ss.append((mod, sx))
            nx = mod.modAtoms[sx].nsibling
            assert not nx or nx > sx, "Bad next-sibling pointer"
            sx = nx
    args2 = pat_match(astargs[subix], ss)
    return None if args2 is None else args + args2

def match_ctor(ctor, args, e):
    nm = getident(ctor)
    if isinstance(e, tuple) and hasattr(e[0], 'modAtoms'):
        return match_array_atom(nm, args, e)
    if CTORS[nm] != e._ix:
        return None
    fs = CTOR_FIELDS[e._ix]
    rs = []
    for f, a in zip(fs, args):
        # XXX: This doesn't work for ArrayAtoms
        if not isinstance(f, basestring):
            f = getname(f)
        r = pat_match(a, getattr(e, f))
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

def expr_and(op, subs, scope):
    for e in match(subs, ('sized(conds)', identity)):
        if not eval_expr(e, scope):
            return False
    return True

def expr_or(op, subs, scope):
    for e in match(subs, ('sized(conds)', identity)):
        if eval_expr(e, scope):
            return True
    return False

def expr_char(op, subs, scope):
    assert isinstance(subs[0], Str) and len(subs[0].strVal) == 1, \
            "'%s' is not a valid char literal" % (subs[0].strVal,)
    return subs[0].strVal

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
        'and': expr_and,
        'or': expr_or,
        'char': expr_char,
    }

def eval_expr(expr, scope):
    nm = match(expr, ('key(nm)', identity), ('_', lambda: None))
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

def shorten(s):
    if len(s) > 140:
        return s[:140] + '...'
    return s

def list_scope(scope):
    additional = ''
    p = scope.prevScope
    if p is not None and p.scopeInfo is not None:
        additional = '\nUnder scope %s:\n%s' % (p.scopeInfo, list_scope(p))
    return '\n'.join('\t%s\t%s' % (getname(k), shorten(str(v)))
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

def stmt_assign(stmt, scope):
    o, left, e = match(stmt, ('key(o, cons(left, cons(e, _)))', tuple3))
    op = {'=': EQUALS, '+=': PLUS_EQUALS, '-=': MINUS_EQUALS}[o]
    do_assign(left, op, eval_expr(e, scope), scope)
    return scope

def enclosing_loop(scope):
    return match(scope.scopeInfo, ('ForScope(_, _, _, _)', lambda: scope),
                                  ('WhileScope(_, _, _)', lambda: scope),
                                  ('CaseScope()',
                                      lambda: enclosing_loop(scope.prevScope)),
                                  ('_', lambda: None))

def stmt_break(stmt, scope):
    scope = enclosing_loop(scope)
    scope.stmtsPos = SCOPE_BREAK
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
    scope.stmtsPos = SCOPE_END
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
    for_scope = new_scope({}, ForScope(a, items, 0, body), body, scope)
    for_scope.stmtsPos = SCOPE_END
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
    this_frame.stmtsPos = SCOPE_BREAK
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

def loop_for(var, list, pos, scope):
    if pos < len(list):
        do_assign(var, EQUALS, list[pos], scope)
        scope.stmtsPos = 0
        scope.scopeInfo.loopPos = pos + 1
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
        if scope.stmtsPos == SCOPE_BREAK or not match(scope.scopeInfo,
                ('WhileScope(c, _)', lambda c: loop_while(c, scope)),
                ('ForScope(v, l, n, _)', lambda v, l, n:
                                         loop_for(v, l, n, scope)),
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

def test(filename):
    module = ast.convert_file(filename)
    f = open('hello', 'w')
    for r in module.roots:
        f.write(repr(r))
    del f, r, filename
    print 'Converted'
    system('rm -f -- mods/*')
    serialize_module(module)
    print 'Serialized'
    serialize_module(ast.convert_file('test.py'))
    print 'Serialized test.py'
    run_module(module)

try:
    import psyco
    psyco.full()
except ImportError:
    pass

if __name__ == '__main__':
    import sys
    filename = sys.argv[1] if len(sys.argv) > 1 else 'interpret.py'
    test(filename)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
