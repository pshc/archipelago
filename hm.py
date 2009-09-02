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
    # XXX: This is very conservative about using bogus constraints
    substs = env.envSubsts
    normalize_substs(substs)
    e1 = apply_substs(substs, e1)
    e2 = apply_substs(substs, e2)
    assert False, "Could not unify %r with %r" % (e1, e2)

def apply_substs_to_func(substs, f, args):
    # Where is your mapM_ now??
    for a in args:
        apply_substs(substs, a)
    return f

def apply_substs(substs, t):
    return match(t, ("key('typevar')", lambda: substs.get(t, t)),
                    ("key('func', sized(args))", lambda args:
                     apply_substs_to_func(substs, t, args)),
                    ("_", lambda: t))

def compose_substs(s1, s2, env):
    s3 = s1.copy()
    for k, v in s2.iteritems():
        if k in s1:
            unify(s1[k], v, env) # This doesn't seem like the right place...
        s3[k] = apply_substs(s1, v)
    return s3

def free_vars_in_func(args):
    # Not bother with reduce and union for ease of C conversion
    fvs = set()
    for a in args:
        fvs.update(free_vars(a))
    return fvs

def free_vars_unknown(k):
    assert False, "Unexpected type '%s' while finding free vars" % (k,)
    return set()

def free_vars(v):
    return match(v, ("key('typevar')", lambda: set([v])),
                    ("key('func', sized(args))", free_vars_in_func),
                    ("key(k)", lambda k: set() if k in basic_types else
                        free_vars_unknown(k)))

def unify_funcs(f1, args1, f2, args2, env):
    if len(args1) != len(args2):
        unification_failure(f1, f2, env)
    substs = {}
    for a1, a2 in zip(args1, args2):
        substs = compose_substs(substs, unify(a1, a2, env), env)
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

def get_type(e, env):
    return env.envTable[e]

def incorporate_substs(substs, env):
    """Actually insert the substs into the environment.

    For now, I'm doing this only once the substitutions hit statement level...
    is it better to do this for all expressions? And what about normalization?
    """
    env.envSubsts = compose_substs(env.envSubsts, substs, env)

def infer_call(f, args, env):
    ft = infer_expr(f, env)
    retT = fresh(env)
    substs = unify(ft, fnT([infer_expr(a, env) for a in args], retT), env)
    incorporate_substs(substs, env)
    return retT

def infer_builtin(k, env):
    if k == '+':
        return fnT([intT(), intT()], intT())
    elif k == '%':
        return fnT([strT(), intT()], strT()) # Bogus!
    elif k == 'print':
        return fnT([strT()], voidT())
    assert False, "Unknown type for builtin '%s'" % (k,)

def unknown_infer(a, env):
    assert False, 'Unknown type for:\n%s' % (a,)

def infer_expr(a, env):
    t = match(a,
        ("Int(_, _)", intT),
        ("Str(_, _)", strT),
        ("key('call', cons(f, sized(s)))", lambda f, s: infer_call(f, s, env)),
        ("key(k)", lambda k: infer_builtin(k, env)),
        ("Ref(v==key('var'), _, _)", lambda v: get_type(v, env)),
        ("otherwise", lambda e: unknown_infer(e, env)))
    #set_type(a, t, env) # Much too noisy
    return t

def infer_DT(fs, nm, env):
    print 'DT', nm

def infer_assign(a, e, env):
    newvar = match(a, ("key('var')", lambda: True),
                      ("Ref(key('var'), _, _)", lambda: False))
    if newvar:
        t = fresh(env)
        set_type(a, t, env)
    else:
        t = get_type(a.refAtom, env)
    substs = unify(t, infer_expr(e, env), env)
    incorporate_substs(substs, env)

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

def write_mod_repr(filename, m):
    f = fopen(filename, 'w')
    for r in m.roots:
        fwrite(f, repr(r))
    fclose(f)

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short)
    infer_types(short.roots)
    write_mod_repr('hello', short)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
