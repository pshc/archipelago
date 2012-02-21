#!/usr/bin/env python2
from atom import *
import sys

IRInfo = DT('IRInfo', ('needIndent', bool), ('tempCtr', int))
IR = new_context('IR', IRInfo)

def setup_ir():
    return IRInfo(False, 0)

Xpr, Reg, Tmp, Const, ConstOp = ADT('Xpr',
        'Reg', ('label', 'str'), ('index', 'int'),
        'Tmp', ('index', 'int'),
        'Const', ('frag', 'str'),
        'ConstOp', ('op', 'str'), ('args', ['Xpr']))

def is_const(x):
    return match(x,
        ('Reg(_, _)', lambda: False), ('Tmp(_)', lambda: False),
        ('Const(_)', lambda: True), ('ConstOp(_, _)', lambda: True))

# OUTPUT

def out(s):
    if context(IR).needIndent:
        sys.stdout.write('  ')
        clear_indent()
    sys.stdout.write(s)

def out_name(a):
    out(extrinsic(Name, a))

def out_name_reg(a):
    out('%%%s' % (extrinsic(Name, a),))

def out_xpr(x):
    out(xpr_str(x))

def xpr_str(x):
    return match(x, ('Reg(nm, i)', lambda nm, i: '%%%s.%d' % (nm, i)),
                    ('Tmp(i)', lambda i: '%%.%d' % (i,)),
                    ('Const(s)', identity),
                    ('ConstOp(f, args)', constop_str))

def constop_str(f, args):
    return '%s (%s)' % (f, ', '.join('i32 %s' % (xpr_str(r),) for r in args))

def clear_indent():
    context(IR).needIndent = False

def newline():
    sys.stdout.write('\n')
    context(IR).needIndent = True

def comma():
    out(', ')

def temp_reg():
    ir = context(IR)
    reg = Tmp(ir.tempCtr)
    ir.tempCtr += 1
    return reg

def temp_reg_named(nm):
    ir = context(IR)
    reg = Reg(nm, ir.tempCtr)
    ir.tempCtr += 1
    return reg

# EXPRESSIONS

def expr_bind_var(v):
    tmp = temp_reg_named(extrinsic(Name, v))
    out_xpr(tmp)
    out(' = load i32* %')
    out_name(v)
    newline()
    return tmp

def expr_bind_func(f):
    return Const('@%s' % (extrinsic(Name, f),))

def bin_op(b):
    # grr boilerplate
    return match(b,
        ('key("+")', lambda: 'add'),
        ('key("-")', lambda: 'sub'),
        ('_', lambda: ''))

def expr_call(f, args):
    m = match(f)
    if m('Bind(BindBuiltin(b))'):
        b = m.arg
        op = bin_op(b)
        assert op != '', 'Unknown builtin %s' % (b,)
        assert len(args) == 2, '%s requires two args' % (op,)
        left = express(args[0])
        right = express(args[1])
        if is_const(left) and is_const(right):
            m.ret(ConstOp(op, [left, right]))
        else:
            tmp = temp_reg_named(op)
            out_xpr(tmp)
            out(' = %s i32 %s, %s' % (op, xpr_str(left), xpr_str(right)))
            newline()
            m.ret(tmp)
    else:
        tmp = temp_reg()
        fx = express(f)
        out_xpr(tmp)
        out(' = call i32 ')
        out_xpr(fx)
        write_args(args)
        newline()
        m.ret(tmp)
    return m.result()

def expr_match(m, e, cs):
    return Const('undefined ;match')
    #for c in cs:
    #cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))

def expr_tuple_lit(ts):
    xs = map(express, ts)
    args = ', '.join('i32 %s' % (xpr_str(x),) for x in xs)
    return Const('{ %s }' % (args,))

def express(expr):
    return match(expr,
        ('Bind(BindVar(v))', expr_bind_var),
        ('Bind(BindFunc(v))', expr_bind_func),
        ('Call(f, args)', expr_call),
        ('m==Match(p, cs)', expr_match),
        ('IntLit(i)', lambda i: Const('%d' % (i,))),
        ('TupleLit(es)', expr_tuple_lit))

# STATEMENTS

def write_defn(v, e):
    ex = express(e)
    out_name_reg(v)
    out(' = alloca i32')
    newline()
    out('store i32 ')
    out_xpr(ex)
    comma()
    out('i32* ')
    out_name_reg(v)

def write_dtstmt(form):
    clear_indent()
    if len(form.ctors) > 1:
        out('; skipping %')
        out_name_reg(form)
    else:
        out_name_reg(form)
        out(' = type { ')
        ctor = form.ctors[0]
        out(', '.join('i32 %s' % (extrinsic(Name, f),) for f in ctor.fields))
        out(' }')

def write_expr_stmt(e):
    out_xpr(express(e))
    newline()

def write_extrinsic_stmt(extr):
    clear_indent()
    out('; extrninsic ')
    out(extrinsic(Name, extr))

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

def write_args(args):
    out('(')
    bits = [express(arg) for arg in args]
    first = True
    for bit in bits:
        if first:
            first = False
        else:
            comma()
        out_xpr(bit)
    out(')')

def write_return(expr):
    ex = express(expr)
    out('ret i32 ')
    out_xpr(ex)

def write_stmt(stmt):
    match(stmt,
        ("Defn(v, e)", write_defn),
        ("DTStmt(form)", write_dtstmt),
        ("ExprStmt(e)", write_expr_stmt),
        ("ExtrinsicStmt(extr)", write_extrinsic_stmt),
        ("FuncStmt(f==Func(ps, body))", write_func_stmt),
        ("Return(e)", write_return))
    newline()

def write_body(body):
    map_(write_stmt, match(body, ('Body(ss)', identity)))

def write_ir(prog):
    in_context(IR, setup_ir(), lambda: write_body(prog))

def main():
    plus = symref('+')
    add = lambda a, b: Call(Bind(BindBuiltin(plus)), [a, b])

    body = []
    func = Func([], Body(body))
    add_extrinsic(Name, func, 'main')
    foo = Var()
    add_extrinsic(Name, foo, 'foo')
    sum = add(Bind(BindVar(foo)), IntLit(1))
    body += [Defn(foo, add(IntLit(40), IntLit(2))),
             Return(sum)]
    write_ir(Body([FuncStmt(func)]))

if __name__ == '__main__':
    main()

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
