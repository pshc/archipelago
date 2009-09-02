#!/usr/bin/env python
from atom import *
from base import *
from builtins import *

Env = DT('Env', ('envTable', {Atom: Atom}),
                ('envSubsts', {Atom: Atom}),
                ('envIndex', int))

map(add_sym, 'type,void,int,bool,char,str,func,typevar,varindex'.split(','))

voidT = lambda: symref('void', [])
intT = lambda: symref('int', [])
boolT = lambda: symref('bool', [])
charT = lambda: symref('char', [])
strT = lambda: symref('str', [])
fnT = lambda args, ret: symref('func', [Int(len(args)+1, [])] + args + [ret])

def fresh(env):
    i = env.envIndex
    env.envIndex = i + 1
    return symref('typevar', [symref('varindex', [Int(i, [])])])

typevar_index = lambda v: match(v, ("key('typevar', cons(key('varindex', "
                                    "cons(Int(ix, _), _)), _))", identity))
def typevars_equal(u, v):
    eq = u is v
    assert eq == (typevar_index(u) == typevar_index(v)) # a true debug assert
    return eq

def unification_failure(e1, e2, env):
    assert ok, "Could not unify %r with %r" % (e1, e2)

def apply_substs(substs, t):
    return substs.get(t, t)

def compose_substs(s1, s2):
    s3 = s1.copy()
    for k, v in s2.iteritems():
        s3[k] = apply_substs(s1, v)
    return s3

def unify_funcs(f1, args1, f2, args2, env):
    if len(args1) != len(args2):
        unification_failure(f1, f2, env)
    substs = {}
    for a1, a2 in zip(args1, args2):
        substs = compose_substs(substs, unify(a1, a2, env))
    return substs

basic_types = ['void', 'int', 'bool', 'char', 'str']

def unify(e1, e2, env):
    return match((e1, e2),
        ("(key('typevar'), key('typevar'))", lambda:
            {} if typevars_equal(e1, e2) else {e1: e2}),
        ("(key('typevar'), _)", lambda: {e1: e2}),
        ("(_, key('typevar'))", lambda: {e2: e1}),
        ("(key('func', sized(a1)), key('func', sized(a2)))",
            lambda a1, a2: unify_funcs(e1, a1, e2, a2, env)),
        # These two must be last
        ("(key(s), key(t))", lambda s, t: {} if s == t and s in basic_types
                             else unification_failure(e1, e2, env)),
        ("_", lambda: unification_failure(e1, e2, env)))

def set_type(e, t, env):
    env.envTable[e] = t

def incorporate_substs(substs, env):
    """Actually insert the substs into the environment.

    For now, I'm doing this only once the substitutions hit statement level...
    is it better to do this for all expressions? And what about normalization?
    """
    env.envSubsts = compose_substs(env.envSubsts, substs)

def infer_call(f, args, env):
    ft = infer_expr(f, env)
    retT = fresh(env)
    substs = unify(ft, fnT([infer_expr(a, env) for a in args], retT), env)
    incorporate_substs(substs, env)
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
    substs = unify(t, infer_expr(e, env), env)
    incorporate_substs(substs, env)
    set_type(a, t, env)

def infer_stmt(a, env):
    match(a,
        ("key('DT', all(fs, key('field') and named(fnm)))"
            " and named(nm)", lambda fs, nm: infer_DT(fs, nm, env)),
        ("key('=', cons(a, cons(e, _)))", lambda a, e: infer_assign(a,e,env)),
        ("key('exprstmt', cons(e, _))", lambda e: infer_expr(e, env)),
        ("otherwise", lambda e: unknown_infer(e, env)))

def normalize_substs(substs):
    """TODO: Correctness... is this even guaranteed to terminate?
             This problem might even be NP-complete AFAIR"""
    changed = True
    ks = dict_keys(substs) # Caution due to dict modification inside loop
    while changed:
        changed = False
        for k in ks:
            v = substs[k]
            if v in substs: # v must be a typevar to be in substs
                v_prime = substs[v]
                if v is not v_prime:
                    substs[k] = v_prime
                    changed = True

def infer_types(roots):
    env = Env({}, {}, 1)
    for r in roots:
        infer_stmt(r, env)
    normalize_substs(env.envSubsts)
    for a, t in env.envTable.iteritems():
        a.subs.append(symref('type', [apply_substs(env.envSubsts, t)]))

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    infer_types(short.roots)
    f = fopen('hello', 'w')
    for r in short.roots:
        fwrite(f, repr(r))
    fclose(f)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent: