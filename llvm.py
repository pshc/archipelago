#!/usr/bin/env python2
from atom import *
import sys

IRInfo = DT('IRInfo', ('needIndent', bool), ('tempCtr', int))
IR = new_context('IR', IRInfo)

def setup_ir():
    return IRInfo(False, 0)

def out(s):
    if context(IR).needIndent:
        sys.stdout.write('  ')
        clear_indent()
    sys.stdout.write(s)

def out_name(a):
    out(extrinsic(Name, a))

def out_name_reg(a):
    out('%')
    out_name(a)

def clear_indent():
    context(IR).needIndent = False

def newline():
    ir = context(IR)
    ir.needIndent = False
    out('\n')
    ir.needIndent = True

def comma():
    out(', ')

def temp_reg_named(base):
    ir = context(IR)
    tmp = ir.tempCtr
    ir.tempCtr += 1
    return '%%%s.%d' % (extrinsic(Name, base), tmp)

def write_bind_var(v):
    tmp = temp_reg_named(v)
    out(tmp)
    out(' = load i32* ')
    out_name_reg(v)
    newline()
    out(tmp)

def write_bind_func(f):
    out('@')
    out_name(f)

def bin_op(b):
    # grr boilerplate
    return match(b,
        ('key("+")', lambda: 'add'),
        ('key("-")', lambda: 'sub'),
        ('_', lambda: ''))

def write_call(f, args):
    def is_builtin(b):
        op = bin_op(b)
        if op != '':
            assert len(args) == 2, '%s requires two args' % (op,)
            out('%s i32 ' % (op,))
            write_expr(args[0])
            comma()
            write_expr(args[1])
            return
        assert False, 'Unknown builtin %s' % (b,)
    def otherwise():
        out('call i32 ')
        write_expr(f)
        write_params(args)
    builtin = match(f, ('Bind(BindBuiltin(b))', is_builtin),
                       ('_', otherwise))

def write_expr(expr):
    match(expr,
        ('Bind(BindVar(v))', write_bind_var),
        ('Bind(BindFunc(v))', write_bind_func),
        ('Call(f, args)', write_call),
        ('IntLit(i)', lambda i: out('i32 %d' % (i,))))

def write_defn(v, e):
    out_name_reg(v)
    out(' = alloca i32')
    newline()
    out('store ')
    write_expr(e)
    comma()
    out('i32* ')
    out_name_reg(v)

def write_func_stmt(f, ps, body):
    clear_indent()
    out('define i32 @')
    out_name(f)
    write_params(ps)
    out(' {\nentry:')
    newline()
    write_body(body)
    clear_indent()
    out('}\n')

def write_param(p):
    # Need type info
    out('i32 ')
    out_name(p)

def write_params(ps):
    out('(')
    if len(ps) > 0:
        write_param(ps[0])
        for p in ps[1:]:
            comma()
            write_param(p)
    out(')')

def write_return(expr):
    out('ret ')
    write_expr(expr)

def write_stmt(stmt):
    match(stmt,
        ("Defn(v, e)", write_defn),
        ("ExprStmt(e)", write_expr),
        ("FuncStmt(f==Func(ps, body))", write_func_stmt),
        ("Return(e)", write_return))
    newline()

def write_body(body):
    map_(write_stmt, match(body, ('Body(ss)', identity)))

def write_ir(prog):
    in_context(IR, setup_ir(), lambda: write_body(prog))

def main():
    body = []
    func = Func([], Body(body))
    add_extrinsic(Name, func, 'main')
    foo = Var()
    add_extrinsic(Name, foo, 'foo')
    plus = symref('+')
    sum = Call(Bind(BindBuiltin(plus)), [Bind(BindVar(foo)), IntLit(1)])
    body += [Defn(foo, IntLit(42)),
             Return(sum)]
    write_ir(Body([FuncStmt(func)]))

if __name__ == '__main__':
    main()

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
