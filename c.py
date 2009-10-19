#!/usr/bin/env python
from base import *
from atom import *
from builtins import *

CEnv = DT('CEnv', ('cenvIndent', int),
                  ('cenvStmts', [Atom]),
                  ('cenvOuterEnv', 'CEnv'))
# The final version of this will thread this state through the functions
# using the type system.
CENV = None

def stmt(s):
    global CENV
    list_append(CENV.cenvStmts, s)
def indent(s):
    global CENV
    i = CENV.cenvIndent
    if i == 0:
        stmt(cat(s, '\n'))
    else:
        stmt(Str('  ' * i, [s, str_('\n')]))
    return None
def blank_line(): stmt(str_('\n'))
def close_brace(): indent(str_('}'))

def bracket(before, c, after):
    assert isinstance(before, basestring)
    assert isinstance(after, basestring)
    return Str(before, [c, str_(after)])
def brackets(before, ss, after):
    assert isinstance(before, basestring)
    assert isinstance(after, basestring)
    return Str(before, ss + [str_(after)])
def cat(a, after):
    assert isinstance(after, basestring)
    list_append(a.subs, str_(after))
    return a
def cats(a, ss):
    assert isinstance(ss, list)
    a.subs += ss
    return a
def semi(): return str_(';')
def comma(): return str_(', ')
def commas(ss):
    assert isinstance(ss, list)
    n = len(ss)
    for s in ss:
        n -= 1
        if n > 0:
            cat(s, ', ')
    return ss

def _c_type(t):
    return match(t,
        ("TInt()", lambda: str_('int')),
        ("TStr()", lambda: str_('char *')),
        ("TTuple(_)", lambda: str_('struct tuple')),
        ("TNullable(v)", _c_type),
        ("TVar(_)", lambda: str_('void *')),
        ("TVoid()", lambda: str_('void')),
        ("TData(named(nm))", lambda nm: bracket('struct ', str_(nm), ' *')))

def c_type(t, tvars):
    return _c_type(atoms_to_type(t, dict((v, TVar(0)) for v in tvars)))

def c_scheme(ta):
    t = atoms_to_scheme(ta)
    return _c_type(t.schemeType)

def c_defref(nm, ss):
    return match(ss,
        ("contains(k==key('unaryop' or 'binaryop' or 'crepr'))", identity),
        ("_", lambda: str_(nm)))

def c_call(f, args):
    cf = c_expr(f)
    cargs = [c_expr(a) for a in args]
    return match(cf,
        ("key('unaryop', cons(s, _))",
            lambda s: cats(s, cargs)),
        ("key('binaryop', cons(Str(s, _), _))",
            lambda s: cats(cargs[0], [str_(' %s ' % (s,)), cargs[1]])),
        ("key('crepr', cons(s, _))",
            lambda s: cats(s, [brackets('(', commas(cargs), ')')])),
        ("_", lambda: cats(cf, [brackets('(', commas(cargs), ')')])))

def c_tuple(ts):
    return brackets('{', commas(map(c_expr, ts)), '}')

def c_expr(e):
    return match(e,
        ("Int(i, _)", lambda i: str_("%d" % (i,))),
        ("Str(s, _)", lambda s: str_(escape_str(s))),
        ("Ref(named(nm, ss==contains(key('type'))), _, _)", c_defref),
        ("Ref(named(nm) and key('ctor', ss), _, _)", c_defref),
        ("key('call', cons(f, sized(args)))", c_call),
        ("key('tuplelit', sized(ts))", c_tuple))

def c_assign(a, e):
    ce = c_expr(e)
    ca = match(a,
        ("key('var', contains(t==key('type'))) and named(nm)",
            lambda t, nm: cat(c_scheme(t), ' %s' % nm)),
        ("Ref(named(nm, contains(key('type'))), _, _)", str_))
    indent(cats(ca, [str_(' = '), ce, semi()]))

def c_cond(subs, cs):
    if_ = 'if ('
    for (t, b) in cs:
        indent(bracket(if_, c_expr(t), ') {'))
        c_body(b)
        close_brace()
        if_ = 'else if ('
    else_ = match(subs, ("contains(key('else', sized(body)))", identity),
                        ("_", lambda: None))
    if else_ is not None:
        indent(str_('else {'))
        c_body(else_)
        close_brace()

def c_while(test, body):
    indent(bracket('while (', c_expr(test), ') {'))
    c_body(body)
    close_brace()

def c_assert(t, m):
    indent(Str("assert(", [c_expr(t), comma(), c_expr(m), str_(');')]))

def c_DT(cs, vs, nm):
    global CENV
    discrim = len(cs) > 1
    blank_line()
    if discrim:
        indent(bracket('struct ', str_(nm), ' {'))
        CENV.cenvIndent += 1
        indent(brackets('enum { ', commas([str_(getname(c)) for c in cs]),
                        ' } ix;'))
        indent(str_('union {'))
        CENV.cenvIndent += 1
    # The actual struct(s)
    ctors = []
    for c in cs:
        cnm, fs = match(c, ("named(nm, all(fs, f==key('field')))", tuple2))
        indent(str_('struct {') if discrim
               else bracket('struct ', str_(cnm), ' {'))
        CENV.cenvIndent += 1
        fields = []
        for f in fs:
            fnm, t = match(f, ("named(nm, contains(key('type', cons(t, _))))",
                               tuple2))
            ct = c_type(t, vs)
            indent(Str('', [ct, bracket(' ', str_(fnm), ';')]))
            fields.append((ct, fnm))
        CENV.cenvIndent -= 1
        indent(bracket('} ', str_(cnm), ';') if discrim else str_('};'))
        ctors.append((cnm, fields))
    if discrim:
        CENV.cenvIndent -= 1
        indent(str_('} c;'))
        CENV.cenvIndent -= 1
        indent(str_('};'))
    # Ctor functions
    for (cnm, fields) in ctors:
        indent(brackets('struct %s * %s(' % (nm, cnm),
                        commas([Str('', [ct, str_(' %s' % fnm)])
                                for (ct, fnm) in fields]),
                       ') {'))
        CENV.cenvIndent += 1
        indent(Str('struct ', map(str_, [nm, ' * s = malloc(sizeof(struct ',
                                         nm, '));'])))
        if discrim:
            indent(bracket('s->ix = ', str_(cnm), ';'))
        for (ct, fnm) in fields:
            if discrim:
                indent(Str('s->c.', map(str_, [cnm,'.',fnm,' = ',fnm,';'])))
            else:
                indent(Str('s->', map(str_, [fnm, ' = ', fnm, ';'])))
        indent(str_('return s;'))
        CENV.cenvIndent -= 1
        close_brace()

def c_args(args):
    return commas([match(a, ("named(nm, contains(t==key('type')))",
                         lambda nm, t: cat(c_scheme(t), ' %s' % (nm,))))
                   for a in args])

def c_func(t, args, body, nm):
    # Wow this is bad
    t_ = atoms_to_scheme(t).schemeType
    retT = c_scheme(scheme_to_atoms(Scheme([], t_.funcRet)))
    blank_line()
    indent(Str('', [retT, str_(' %s(' % (nm,))]
                          + c_args(args) + [str_(') {')]))
    c_body(body)
    close_brace()

def c_stmt(s):
    match(s,
        ("key('exprstmt', cons(e, _))",
            lambda e: indent(cat(c_expr(e), ';'))),
        ("key('=', cons(a, cons(e, _)))", c_assign),
        ("key('cond', ss and all(cs, key('case', cons(t, sized(b)))))",c_cond),
        ("key('while', cons(t, contains(key('body', sized(b)))))", c_while),
        ("key('assert', cons(t, cons(m, _)))", c_assert),
        ("key('DT', all(cs, c==key('ctor'))\
                and all(vs, v==key('typevar'))) and named(nm)", c_DT),
        ("key('func', contains(t==key('type')) "
                 "and contains(key('args', sized(a))) "
                 "and contains(key('body', sized(b)))) and named(nm)", c_func),
        ("key('return', cons(e, _))",
            lambda e: indent(bracket("return ", c_expr(e), ';'))),
        ("key('returnnothing')", lambda: indent(str_("return;"))))

def c_body(ss):
    global CENV
    corig = CENV
    CENV = CEnv(corig.cenvIndent + 1, [], corig)
    for s in ss:
        c_stmt(s)
    assert corig is CENV.cenvOuterEnv
    corig.cenvStmts += CENV.cenvStmts
    CENV = corig

def generate_c(mod):
    global CENV
    CENV = CEnv(-1, [], None)
    c_body(mod.roots)
    return Module("c_" + mod.name, None, CENV.cenvStmts)

def _write_c_strs(f, atom):
    assert isinstance(atom, Str), "Need Str, got: %s" % (atom,)
    fwrite(f, atom.strVal)
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
