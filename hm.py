#!/usr/bin/env python
from atom import *
from base import *
from builtins import *

Env = DT('Env', ('envTable', {Atom: Atom}))

map(add_sym, 'type,void,int,bool,char,str,func,typevar'.split(','))

voidT = lambda: symref('void', [])
intT = lambda: symref('int', [])
boolT = lambda: symref('bool', [])
charT = lambda: symref('char', [])
strT = lambda: symref('str', [])
fnT = lambda args, ret: symref('func', [Int(len(args)+1, [])] + args + [ret])

def fresh(env):
    return symref('typevar', [])

basic_types = set(['void', 'int', 'bool', 'char', 'str'])

def unify(e1, e2, env):
    # TODO: substs
    ok = match((e1, e2),
            ("(key('typevar'), _)", lambda: True),
            ("(_, key('typevar'))", lambda: True),
            ("(key('func', sized(ss)), key('func', sized(ts)))",
                lambda ss, ts: len(ss) == len(ts) and
                               all(unify(s, t, env) for s, t in zip(ss, ts))),
            # These two must be last
            ("(key(s), key(t))", lambda s, t: s == t and s in basic_types),
            ("_", lambda: False))
    assert ok, "Could not unify %r with %r" % (e1, e2)
    return True

def set_type(e, t, env):
    env.envTable[e] = t

def infer_call(f, args, env):
    ft = infer_expr(f, env)
    retT = fresh(env)
    unify(ft, fnT([infer_expr(a, env) for a in args], retT), env)
    return retT

def infer_builtin(k, env):
    if k == '+':
        return fnT([intT(), intT()], intT())

def unknown_infer(a, env):
    assert False, 'Unknown type for:\n%s' % (a,)

def infer_expr(a, env):
    t = match(a,
        ("Int(_, _)", intT),
        ("Str(_, _)", strT),
        ("key('call', cons(f, sized(s)))", lambda f, s: infer_call(f, s, env)),
        ("key(k)", lambda k: infer_builtin(k, env)),
        ("otherwise", lambda e: unknown_infer(e, env)))
    set_type(a, t, env)
    return t

def infer_DT(fs, nm, env):
    print 'DT', nm

def infer_assign(a, e, env):
    newvar = match(a, ("key('var')", lambda: True), ("_", lambda: False))
    assert newvar
    t = fresh(env)
    unify(t, infer_expr(e, env), env)
    set_type(a, t, env)

def infer_stmt(a, env):
    match(a,
        ("key('DT', all(fs, key('field') and named(fnm)))"
            " and named(nm)", lambda fs, nm: infer_DT(fs, nm, env)),
        ("key('=', cons(a, cons(e, _)))", lambda a, e: infer_assign(a,e,env)),
        ("key('exprstmt', cons(e, _))", lambda e: infer_expr(e, env)),
        ("otherwise", lambda e: unknown_infer(e, env)))

def infer_types(roots):
    env = Env({})
    for r in roots:
        infer_stmt(r, env)
    for a, t in env.envTable.iteritems():
        a.subs.append(symref('type', [t]))

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    infer_types(short.roots)
    f = fopen('hello', 'w')
    for r in short.roots:
        fwrite(f, repr(r))
    fclose(f)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
