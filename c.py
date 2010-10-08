#!/usr/bin/env python
from base import *
from atom import *
from builtins import *
import sys

CEnv = DT('CEnv', ('cenvIndent', int),
                  ('cenvHandle', None),
                  ('cenvOuterEnv', 'CEnv'))
# The final version of this will thread this state through the functions
# using the type system.
CENV = None

def out(s):
    global CENV
    assert isinstance(s, basestring), "Expected string, got: %s" % (s,)
    sys.stdout.write(s)
    fwrite(CENV.cenvHandle, s)
def indent():
    global CENV
    out('  ' * CENV.cenvIndent)
def open_brace():
    out(') {\n')
def close_brace():
    indent()
    out('}\n')
def semicolon():
    out(';\n')

def comma_exprs(es):
    n = len(es)
    for e in es:
        c_expr(e)
        n -= 1
        if n > 0:
            out(', ')

def parens(f): out('('); f(); out(')')
def brackets(f): out('{'); f(); out('}')

def out_Str(s):
    match(s, ("Str(s, _)", out), ("Ref(Str(s, _), _)", out))

def c_ptr(t): c_type(t); out('*')
def c_structref(s): out('struct '); out_Str(s)

def c_struct(s, k, fs):
    out(k)
    out(' ')
    nm = match(s, ("named(nm)", identity), ("_", lambda: None))
    if nm is not None:
        out(nm)
        out(' ')
    out('{\n')
    c_body(fs)
    indent()
    out('}')

def c_type(t):
    match(t,
        ("key(prim==('int' or 'char' or 'void'))", out),
        ("key(TODO==('somefunc_t'))", out),
        ("key('ptr', cons(t, _))", c_ptr),
        ("key('structref', cons(s, _))", c_structref),
        ("Ref(key('typedef', cons(_, cons(nm, _))), _)", out_Str),
        ("s==key(k==('struct' or 'union' or 'enum'), "
                "all(fs, f==key('field' or 'enumerator')))", c_struct))

def typed_name(t, nm):
    c_type(t)
    out(' ')
    out_Str(nm)

def just_identifier(e):
   return match(e, ('Str(s, _)', identity),
                   ('Ref(Str(s, _), _)', identity),
                   ('_', lambda: None))

unary_ops = {'negate': '-'}
binary_ops = {'+': ' + ', '*': ' * ', '.': '.', '->': '->', '==': ' == ',
        '&&': ' && '}

def c_call(f, args):
    s = just_identifier(f)
    n = len(args)
    if s is None: # Not just a named function... parens to be safe
        parens(lambda: c_expr(f))
    elif n == 1 and s in unary_ops:
        out(unary_ops[s])
        c_expr(args[0])
        return
    elif n == 2 and s in binary_ops:
        # TODO: Operator precedence
        c_expr(args[0])
        out(binary_ops[s])
        c_expr(args[1])
        return
    elif n == 3 and s == '?:':
        c_expr(args[0])
        out(' ? ')
        c_expr(args[1])
        out(' : ')
        c_expr(args[2])
        return
    else:
        out(s)
    parens(lambda: comma_exprs(args))

def c_sizeof(t):
    out('sizeof(')
    c_type(t)
    out(')')

def c_sizeof_expr(e):
    s = just_identifier(e)
    if s is None:
        out('sizeof(')
        c_expr(e)
        out(')')
    else: # XXX: This isn't operator-precedence safe
        out('sizeof ')
        c_expr(e)

def c_op(op, ss):
    if op in unary_ops:
        out(unary_ops[op])
        c_expr(ss[0])
    elif op in binary_ops:
        c_expr(ss[0])
        out(binary_ops[op])
        c_expr(ss[1])
    elif op == 'subscript':
        c_expr(ss[0])
        out('[')
        c_expr(ss[1])
        out(']')
    elif op == ':?':
        c_expr(ss[0])
        out(' ? ')
        c_expr(ss[1])
        out(' : ')
        c_expr(ss[2])
    else:
        assert False, 'Unknown C op: %s' % (op,)

def c_expr(e):
    match(e,
        ("Int(i, _)", lambda i: out("%d" % (i,))),
        ("Str(s, _)", out),
        ("Ref(Str(s, _), _)", out),
        ("key('strlit', cons(Str(s, _), _))",
            lambda s: out(escape_str(s))),
        ("key('call', cons(f, sized(args)))", c_call),
        ("key('tuplelit', sized(ts))",
            lambda ts: brackets(lambda: comma_exprs(ts))),
        ("key('sizeof', cons(t, _))", c_sizeof),
        ("key('sizeofexpr', cons(e, _))", c_sizeof_expr),
        ("key('NULL')", lambda: out("NULL")), # XXX: stupid special case
        ("key(op, ss)", c_op))

def c_exprstmt(e):
    indent()
    c_expr(e)
    out(';\n')

def c_assign(a, e):
    indent()
    c_expr(a)
    out(' = ')
    c_expr(e)
    semicolon()

def c_decl(t):
    indent()
    c_type(t)
    semicolon()

def c_vardecl(nm, t):
    indent()
    typed_name(t, nm)
    semicolon()

def c_vardefn(nm, t, e):
    indent()
    typed_name(t, nm)
    out(' = ')
    c_expr(e)
    semicolon()

def c_typedef(t, nm):
    indent()
    out('typedef ')
    c_type(t)
    out(' ')
    out_Str(nm)
    semicolon()

def c_if(subs, cs):
    if_ = 'if ('
    for (t, b) in cs:
        indent()
        out(if_)
        c_expr(t)
        open_brace()
        c_body(b)
        close_brace()
        if_ = 'else if ('
    else_ = match(subs, ("contains(key('else', sized(body)))", identity),
                        ("_", lambda: None))
    if else_ is not None:
        indent()
        out('else {\n')
        c_body(else_)
        close_brace()

def c_while(test, body):
    indent()
    out('while (')
    c_expr(test)
    open_brace()
    c_body(body)
    close_brace()

def c_func(ss, retT, nm, args, body):
    indent()
    if match(ss, ("contains(key('static'))", lambda: True),
                 ("_", lambda: False)):
        out('static ')
    typed_name(retT, nm)
    out('(')
    n = len(args)
    for a in args:
        match(a, ("key('arg', cons(t, cons(nm, _)))", typed_name))
        n -= 1
        if n > 0:
            out(', ')
    open_brace()
    c_body(body)
    close_brace()

def c_return(e):
    indent()
    out('return')
    if e is not None:
        out(' ')
        c_expr(e)
    semicolon()

def c_field(t, nm):
    indent()
    typed_name(t, nm)
    semicolon()

def c_enumerator(nm):
    indent()
    out_Str(nm)
    out(',\n')

def c_include(filename, angle_brackets):
    out('#include <' if angle_brackets else '#include "')
    out_Str(filename)
    out('>\n' if angle_brackets else '"\n')

def c_comment(s):
    indent()
    out('/* ')
    out_Str(s)
    out(' */\n')

def c_stmt(s):
    match(s,
        ("key('exprstmt', cons(e, _))", c_exprstmt),
        ("key('=', cons(a, cons(e, _)))", c_assign),
        ("key('decl', cons(t, _))", c_decl),
        ("key('vardecl', cons(nm, cons(t, _)))", c_vardecl),
        ("key('vardefn', cons(nm, cons(t, cons(e, _))))", c_vardefn),
        ("key('typedef', cons(t, cons(nm, _)))", c_typedef),
        ("key('if', ss and all(cs, key('case', cons(t, sized(b)))))", c_if),
        ("key('while', cons(t, sized(b)))", c_while),
        ("key('func', ss==cons(retT, cons(nm, "
                 "contains(key('args', sized(a))) and "
                 "contains(key('body', sized(b))))))", c_func),
        ("key('return', cons(e, _))", c_return),
        ("key('returnnothing')", lambda: c_return(None)),
        ("key('field', cons(t, cons(nm, _)))", c_field),
        ("key('enumerator', cons(nm, _))", c_enumerator),
        ("key('includesys', cons(file, _))", lambda f: c_include(f, True)),
        ("key('includelocal', cons(file, _))", lambda f: c_include(f, False)),
        ("key('comment', cons(s, _))", c_comment),
        )

def c_body(ss):
    global CENV
    corig = CENV
    CENV = CEnv(corig.cenvIndent + 1, corig.cenvHandle, corig)
    for s in ss:
        c_stmt(s)
    assert corig is CENV.cenvOuterEnv
    CENV = corig

def write_c_file(filename, mod):
    global CENV
    f = fopen(filename, 'w')
    CENV = CEnv(-1, f, None)
    c_body(mod.roots)
    fclose(f)

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    write_mod_repr('hello', short, [])
    write_mod_repr('konnichiwa', short, [])
    serialize_module(boot_mod)
    serialize_module(short)
    import hm
    types = hm.infer_types(short.roots)
    write_mod_repr('konnichiwa', short, [types])
    print 'Inferred types.'
    print
    print 'Generating C...'
    print '==============='
    from mogrify import mogrify
    c = mogrify(short, types)
    write_mod_repr('hello', c, [])
    write_c_file('world.c', c)
    serialize_module(c)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
