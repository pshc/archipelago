#!/usr/bin/env python
from base import *
from atom import *
from builtins import *

def c_type(ta):
    t = atoms_to_scheme(ta)
    return match(t.schemeType,
        ("TInt()", lambda: 'int'),
        ("TStr()", lambda: 'char *'),
        ("TTuple(_)", lambda: 'struct tuple'),
        ("TNullable()", lambda: 'void *'))

def c_defref(nm, ss):
    return match(ss,
        ("contains(key('unaryop', cons(Str(s, _), _)))",
            lambda s: '%s%%s' % (s,)),
        ("contains(key('binaryop', cons(Str(s, _), _)))",
            lambda s: '%%s %s %%s' % (s.replace('%', '%%'),)),
        ("contains(key('crepr', cons(Str(s, _), _)))", identity),
        ("_", lambda: nm))

def c_call(f, args):
    cf = c_expr(f)
    cargs = map(c_expr, args)
    if cf.startswith('%'): # op
        return cf % tuple(cargs)
    else:
        return '%s(%s)' % (cf, ', '.join(cargs))

def c_tuple(ts):
    return '{%s}' % (', '.join(c_expr(t) for t in ts),)

def c_expr(e):
    return match(e,
        ("Int(i, _)", lambda i: "%d" % (i,)),
        ("Str(s, _)", lambda s: escape_str(s)),
        ("Ref(named(nm, ss==contains(key('type'))), _, _)", c_defref),
        ("key('call', cons(f, sized(args)))", c_call),
        ("key('tuplelit', sized(ts))", c_tuple))

def c_assign(a, e):
    ce = c_expr(e)
    ca = match(a,
        ("key('var', contains(t==key('type'))) and named(nm)",
            lambda t, nm: '%s %s' % (c_type(t), nm)),
        ("Ref(named(nm, contains(key('type'))), _, _)", identity))
    return '%s = %s;' % (ca, ce)

def c_cond(cs):
    first = True
    ss = []
    for (t, b) in cs:
        s = ''
        if match(t, ("key('else')", lambda: False), ("_", lambda: True)):
            s = '%s (%s) {\n' % ('if' if first else 'else if', c_expr(t))
            first = False
        else:
            assert not first
            s = 'else {\n'
        list_append(ss, s)
        ss += c_body(b)
        list_append(ss, '\n}\n')
    return ''.join(ss)

def c_assert(t, m):
    return "assert(%s, %s);" % (c_expr(t), c_expr(m))

def c_stmt(s):
    return match(s,
        ("key('exprstmt', cons(e, _))", lambda e: '%s;' % (c_expr(e),)),
        ("key('=', cons(a, cons(e, _)))", c_assign),
        ("key('cond', all(cs, key('case', cons(t, sized(b)))))", c_cond),
        ("key('assert', cons(t, cons(m, _)))", c_assert),
        ("key('DT') and named(nm)", lambda nm: "struct %s {};" % (nm,)))

def c_body(ss):
    return [c_stmt(s) for s in ss]

def generate_c(mod):
    rs = [Str(s, []) for s in c_body(mod.roots)]
    return Module("c_" + mod.name, None, rs)

def _write_c_strs(f, atom):
    fwrite(f, atom.strVal)
    fputc(f, '\n')
    for sub in atom.subs:
        _write_c_strs(f, sub)

def write_c_file(filename, mod):
    f = fopen(filename, 'w')
    for root in mod.roots:
        _write_c_strs(f, root)
    fclose(f)

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short)
    import hm
    hm.infer_types(short.roots)
    write_mod_repr('hello', short)
    print 'Inferred types.'
    c = generate_c(short)
    write_c_file('world', c)
    print 'Generated C.'
    print '============'
    print file('world').read()
    serialize_module(short)
    serialize_module(c)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
