#!/usr/bin/env python
from atom import *
from base import *
from builtins import *

map(add_sym, 'type,void,int,bool,char,str,func,typevar'.split(','))

voidT = lambda: symref('void', [])
intT = lambda: symref('int', [])
boolT = lambda: symref('bool', [])
charT = lambda: symref('char', [])
strT = lambda: symref('str', [])
fnT = lambda args, ret: symref('func', [Int(len(args)+1, [])] + args + [ret])

def fresh():
    return symref('typevar', [])

basic_types = set(['void', 'int', 'bool', 'char', 'str'])

def unify(e1, e2):
    # TODO: env, substs
    ok = match((e1, e2),
            ("(key('typevar'), _)", lambda: True),
            ("(_, key('typevar'))", lambda: True),
            ("(key('func', sized(ss)), key('func', sized(ts)))",
                lambda ss, ts: len(ss) == len(ts)
                               and all(unify(s, t) for s, t in zip(ss, ts))),
            # These two must be last
            ("(key(s), key(t))", lambda s, t: s == t and s in basic_types),
            ("_", lambda: False))
    assert ok, "Could not unify %r with %r" % (e1, e2)
    return True

def set_type(e, t):
    e.subs.append(symref('type', [t]))

def infer_call(f, args):
    ft = infer_expr(f)
    retT = fresh()
    unify(ft, fnT(map(infer_expr, args), retT))
    return retT

def infer_builtin(k):
    if k == '+':
        return fnT([intT(), intT()], intT())

def unknown_infer(a):
    assert False, 'Unknown type for:\n%s' % (a,)

def infer_expr(a):
    t = match(a,
        ("Int(_, _)", intT),
        ("Str(_, _)", strT),
        ("key('call', cons(f, sized(args)))", infer_call),
        ("key(k)", infer_builtin),
        ("otherwise", unknown_infer))
    set_type(a, t)
    return t

def infer_DT(fs, nm):
    print 'DT', nm

def infer_assign(a, e):
    newvar = match(a, ("key('var')", lambda: True), ("_", lambda: False))
    assert newvar
    t = fresh()
    unify(t, infer_expr(e))
    set_type(a, t)

def infer_exprstmt(e):
    infer_expr(e) # discard type

def infer_stmt(a):
    match(a,
        ("key('DT', all(fs, key('field') and named(fnm)))"
            " and named(nm)", infer_DT),
        ("key('=', cons(a, cons(e, _)))", infer_assign),
        ("key('exprstmt', cons(e, _))", infer_exprstmt),
        ("otherwise", unknown_infer))

def infer_types(roots):
    for r in roots:
        infer_stmt(r)

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    infer_types(short.roots)
    f = fopen('hello', 'w')
    for r in short.roots:
        fwrite(f, repr(r))
    fclose(f)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
