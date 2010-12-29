#!/usr/bin/env python2
from base import *
from atom import *
import sys

CEnv = DT('CEnv', ('cenvIndent', int),
                  ('cenvOuterEnv', 'CEnv'))
# The final version of this will thread this state through the functions
# using the type system.
CENV = None

CENV_C_HANDLE = None
CENV_H_HANDLE = None
CENV_CUR_HANDLE = None

def out(s):
    global CENV_CUR_HANDLE
    assert isinstance(s, basestring), "Expected string, got: %s" % (s,)
    if CENV_CUR_HANDLE == CENV_C_HANDLE:
        sys.stdout.write(s)
    CENV_CUR_HANDLE.write(s)
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

def begin_header():
    global CENV_CUR_HANDLE, CENV_H_HANDLE
    assert CENV_CUR_HANDLE != CENV_H_HANDLE
    CENV_CUR_HANDLE = CENV_H_HANDLE
def end_header():
    global CENV_CUR_HANDLE, CENV_C_HANDLE
    assert CENV_CUR_HANDLE != CENV_C_HANDLE
    CENV_CUR_HANDLE = CENV_C_HANDLE
def is_global_scope():
    global CENV
    return CENV.cenvIndent == 0

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
    nm = match(s.subs,
            ("contains(sym('csyms', 'name', cons(nm, _)))", just_identifier),
            ("_", lambda: None))
    if nm is not None:
        out(nm)
        out(' ')
    out('{\n')
    c_body(fs)
    indent()
    out('}')

def c_type(t):
    match(t,
        ("sym('csyms', prim==('int' or 'char' or 'void'))", out),
        ("sym('csyms', TODO==('func_t' or 'tuple_t'))", out),
        ("sym('csyms', 'ptr', cons(t, _))", c_ptr),
        ("sym('csyms', 'structref', cons(s, _))", c_structref),
        ("Ref(sym('csyms', 'typedef', cons(_, cons(nm, _))), _)", out_Str),
        ("s==sym('csyms', k==('struct' or 'union' or 'enum'), "
            "all(fs, f==sym('csyms', 'field' or 'enumerator')))", c_struct))

def typed_name(t, nm):
    c_type(t)
    out(' ')
    out_Str(nm)

def just_identifier(e):
   return match(e, ('Str(s, _)', identity),
                   ('Ref(Str(s, _), _)', identity),
                   ('_', lambda: None))

unary_ops = {'negate': '-', 'addrof': '&', 'deref': '*'}
binary_ops = {'+': ' + ', '-': ' - ', '*': ' * ', '/': ' / ',
        '.': '.', '->': '->',
        '==': ' == ', '!=': ' != ', '<': ' < ', '>': ' > ',
        '&&': ' && ', '||': ' || '}

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

def c_cast(t, e):
    out('(')
    c_type(t)
    out(') ')
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
        ("sym('csyms', 'strlit', cons(Str(s, _), _))",
            lambda s: out(escape_str(s))),
        ("sym('csyms', 'call', cons(f, sized(args)))", c_call),
        ("sym('csyms', 'tuplelit', sized(ts))",
            lambda ts: brackets(lambda: comma_exprs(ts))),
        ("sym('csyms', 'sizeof', cons(t, _))", c_sizeof),
        ("sym('csyms', 'sizeofexpr', cons(e, _))", c_sizeof_expr),
        ("sym('csyms', 'NULL')", lambda: out("NULL")), # XXX: dumb special case
        ("sym('csyms', 'cast', cons(t, cons(e, _)))", c_cast),
        ("sym('csyms', op, ss)", c_op))

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
    if is_global_scope():
        begin_header()

    indent()
    c_type(t)
    semicolon()

    if is_global_scope():
        end_header()

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
    begin_header()

    indent()
    out('typedef ')
    c_type(t)
    out(' ')
    out_Str(nm)
    semicolon()

    end_header()

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
    else_ = match(subs, ("contains(sym('csyms', 'else', sized(body)))",
                            identity),
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

def c_func_args(args):
    n = len(args)
    if n == 0:
        out('void')
    for a in args:
        match(a, ("sym('csyms', 'arg', cons(t, cons(nm, _)))", typed_name))
        n -= 1
        if n > 0:
            out(', ')

def c_func(ss, retT, nm, args, body):
    is_static = match(ss, ("contains(sym('csyms', 'static'))", lambda: True),
                          ("_", lambda: False))
    if not is_static and is_global_scope():
        begin_header()
        typed_name(retT, nm)
        out('(')
        c_func_args(args)
        out(')')
        semicolon()
        end_header()

    indent()
    if is_static:
        out('static ')
    typed_name(retT, nm)
    out('(')
    c_func_args(args)
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
    if angle_brackets:
        out('#include <')
        out_Str(filename)
        out('>\n')
    else:
        begin_header()
        out('#include "')
        out_Str(filename)
        out('"\n')
        end_header()

def c_comment(s):
    indent()
    out('/* ')
    out_Str(s)
    out(' */\n')

def c_stmt(s):
    match(s,
        ("sym('csyms', 'exprstmt', cons(e, _))", c_exprstmt),
        ("sym('csyms', '=', cons(a, cons(e, _)))", c_assign),
        ("sym('csyms', 'decl', cons(t, _))", c_decl),
        ("sym('csyms', 'vardecl', cons(nm, cons(t, _)))", c_vardecl),
        ("sym('csyms', 'vardefn', cons(nm, cons(t, cons(e, _))))", c_vardefn),
        ("sym('csyms', 'typedef', cons(t, cons(nm, _)))", c_typedef),
        ("sym('csyms', 'if', ss and "
            "all(cs, sym('csyms', 'case', cons(t, sized(b)))))", c_if),
        ("sym('csyms', 'while', cons(t, sized(b)))", c_while),
        ("sym('csyms', 'func', ss==cons(retT, cons(nm, "
                 "contains(sym('csyms', 'args', sized(a))) and "
                 "contains(sym('csyms', 'body', sized(b))))))", c_func),
        ("sym('csyms', 'return', cons(e, _))", c_return),
        ("sym('csyms', 'returnnothing')", lambda: c_return(None)),
        ("sym('csyms', 'field', cons(t, cons(nm, _)))", c_field),
        ("sym('csyms', 'enumerator', cons(nm, _))", c_enumerator),
        ("sym('csyms', 'includesys', cons(file, _))",
            lambda f: c_include(f, True)),
        ("sym('csyms', 'includelocal', cons(file, _))",
            lambda f: c_include(f, False)),
        ("sym('csyms', 'comment', cons(s, _))", c_comment),
        )

def c_body(ss):
    global CENV
    corig = CENV
    CENV = CEnv(corig.cenvIndent + 1, corig)
    for s in ss:
        c_stmt(s)
    assert corig is CENV.cenvOuterEnv
    CENV = corig

def write_c(mod, dir):
    global CENV, CENV_C_HANDLE, CENV_H_HANDLE, CENV_CUR_HANDLE
    name = mod.name[2:]
    CENV_C_HANDLE = open('%s/%s.c' % (dir, name), 'w')
    CENV_H_HANDLE = open('%s/%s.h' % (dir, name), 'w')
    CENV_CUR_HANDLE = CENV_C_HANDLE
    CENV = CEnv(-1, None)

    name_def = name.upper()

    begin_header()
    out('#ifndef %s_H\n#define %s_H\n\n' % (name_def, name_def))
    end_header()

    out('#include "%s.h"\n' % (name,))
    c_body(mod.roots)

    begin_header()
    out('\n#endif\n')
    end_header()

    CENV_H_HANDLE.close()
    CENV_C_HANDLE.close()

def compile_module(filename):
    mod, deps = load_module(filename)
    src = cons('support/archipelago.c', ['views/%s.c' % d.name for d in deps])
    out = 'views/%s' % mod.name
    import subprocess
    try:
        subprocess.check_call(['gcc', '-o', out, '-Isupport', '-Iviews'] + src)
    except subprocess.CalledProcessError, e:
        print '`%s` returned %d' % (' '.join(e.cmd), e.returncode)

if __name__ == '__main__':
    import sys
    for filename in sys.argv[1:]:
        compile_module(filename)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
