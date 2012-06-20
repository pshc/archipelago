from atom import *
import expand
import sys

IRInfo = DT('IRInfo', ('stream', None),
                      ('needIndent', bool),
                      ('lcCtr', int))
IR = new_env('IR', IRInfo)

IRLocals = DT('IRLocals', ('tempCtr', int),
                          ('labelCtr', int),
                          ('loopLabels', 'Maybe((Label, Label))'))

LOCALS = new_env('LOCALS', IRLocals)

def setup_ir(filename):
    stream = file(filename, 'wb') # really ought to close explicitly
    return IRInfo(stream, False, 0)

def setup_locals():
    return IRLocals(0, 0, Nothing())

Xpr, Reg, Tmp, Const, ConstOp = ADT('Xpr',
        'Reg', ('label', 'str'), ('index', 'int'),
        'Tmp', ('index', 'int'),
        'Const', ('frag', 'str'),
        'ConstOp', ('op', 'str'), ('args', ['Xpr']))

def is_const(x):
    return match(x,
        ('Reg(_, _)', lambda: False), ('Tmp(_)', lambda: False),
        ('Const(_)', lambda: True), ('ConstOp(_, _)', lambda: True))

BindingReplacement = DT('BindingReplacement', ('replacement', Xpr))
Replacement = new_extrinsic('Replacement', BindingReplacement)

Label = DT('Label', ('name', str), ('index', int))

# OUTPUT

def stdout(s):
    if not env(GENOPTS).quiet:
        sys.stdout.write(s)

def out(s):
    ir = env(IR)
    if ir.needIndent:
        ir.stream.write('  ')
        stdout('  ')
        clear_indent()
    ir.stream.write(s)
    stdout(s)

def out_name(a):
    out(extrinsic(Name, a))

def out_name_reg(a):
    out('%%%s' % (extrinsic(Name, a),))

def func_ref(f):
    if not has_extrinsic(Name, f):
        add_extrinsic(Name, f, "unnamed_func")
    return '@%s' % (extrinsic(Name, f),)

def global_ref(v):
    return '@%s' % (extrinsic(Name, v),)

def out_func_ref(f):
    out(func_ref(f))

def out_label(label):
    clear_indent()
    out('%s_%d:' % (label.name, label.index))
    newline()

def out_label_ref(label):
    out('label %%%s_%d' % (label.name, label.index))

def out_br_label(label):
    out('br ')
    out_label_ref(label)
    newline()

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
    env(IR).needIndent = False

def newline():
    if env(GENOPTS).quiet:
        return
    ir = env(IR)
    ir.stream.write('\n')
    stdout('\n')
    ir.needIndent = True

def comma():
    out(', ')

def temp_reg():
    lcl = env(LOCALS)
    reg = Tmp(lcl.tempCtr)
    lcl.tempCtr += 1
    return reg

def temp_reg_named(nm):
    lcl = env(LOCALS)
    reg = Reg(nm, lcl.tempCtr)
    lcl.tempCtr += 1
    return reg

def new_label(nm):
    lcl = env(LOCALS)
    label = Label(nm, lcl.labelCtr)
    lcl.labelCtr += 1
    return label

# TYPES

IType, IInt, IPtr, IVoidPtr = ADT('IType',
        'IInt',
        'IPtr', ('type', 'IType'),
        'IVoidPtr')

def typeof(e):
    if has_extrinsic(TypeOf, e):
        return match(extrinsic(TypeOf, e),
            ("TPrim(PInt())", lambda: IInt()),
            ("TVar(_)", lambda: IVoidPtr()),
            ("TFunc(_, _)", lambda: IVoidPtr()))
    def no_type():
        print 'HAS NO TYPEOF: %s' % (e,)
        return IInt()
    return match(e,
        ("IntLit(_)", lambda: IInt()),
        ("_", no_type))

def t_str(t):
    return match(t,
        ("IInt()", lambda: "i32"),
        ("IPtr(p)", lambda p: t_str(p) + "*"),
        ("IVoidPtr()", lambda: "i8*"))

def out_t(t):
    out('%s ' % (t_str(t),))
def out_t_ptr(t):
    out('%s* ' % (t_str(t),))
def out_t_nospace(t):
    out(t_str(t))

# EXPRESSIONS

def expr_bind_builtin(b):
    return match(b,
        ('key("True")', lambda: Const('1')),
        ('key("False")', lambda: Const('0')))

def expr_bind_ctor(c):
    return Const(func_ref(c))

def expr_bind_var(v):
    if has_extrinsic(Replacement, v):
        return extrinsic(Replacement, v)
    tmp = temp_reg_named(extrinsic(Name, v))
    out_xpr(tmp)
    out(' = load ')
    out_t_ptr(typeof(v))
    out_name_reg(v)
    newline()
    return tmp

def bin_op(b):
    # grr boilerplate
    return match(b,
        ('key("+")', lambda: 'add'),
        ('key("-")', lambda: 'sub'),
        ('key("*")', lambda: 'mul'),
        ('key("==")', lambda: 'icmp eq'), ('key("!=")', lambda: 'icmp ne'),
        ('key("<")', lambda: 'icmp slt'), ('key(">")', lambda: 'icmp sgt'),
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
            tmp = temp_reg_named(op.split(' ')[-1])
            out_xpr(tmp)
            out(' = %s i32 %s, %s' % (op, xpr_str(left), xpr_str(right)))
            newline()
            m.ret(tmp)
    else:
        tmp = temp_reg()
        fx = express(f)
        argxs = [express(arg) for arg in args]
        out_xpr(tmp)
        out(' = call i32 ')
        out_xpr(fx)
        write_xpr_list(argxs)
        newline()
        m.ret(tmp)
    return m.result()

def write_xpr_list(args):
    out('(')
    first = True
    for arg in args:
        if first:
            first = False
        else:
            comma()
        out('i32 ')
        out_xpr(arg)
    out(')')

def expr_func(f, ps, body):
    clos = extrinsic(expand.Closure, f)
    assert not clos.isClosure, "TODO"
    return Const(func_ref(clos.func))

def expr_match(m, e, cs):
    return Const('undefined ;match')
    #for c in cs:
    #cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))

def expr_strlit(lit):
    info = extrinsic(expand.ExpandedDecl, lit)
    tmp = temp_reg()
    out_xpr(tmp)
    out(' = getelementptr [0 x i8]* %s, i32 0, i32 0' %
            (global_ref(info.var),))
    newline()
    return tmp

def expr_tuple_lit(ts):
    xs = map(express, ts)
    args = ', '.join('i32 %s' % (xpr_str(x),) for x in xs)
    return Const('{ %s }' % (args,))

def express(expr):
    return match(expr,
        ('Bind(BindBuiltin(b))', expr_bind_builtin),
        ('Bind(BindCtor(c))', expr_bind_ctor),
        ('Bind(BindVar(v))', expr_bind_var),
        ('Call(f, args)', expr_call),
        ('FuncExpr(f==Func(ps, body))', expr_func),
        ('m==Match(p, cs)', expr_match),
        ('IntLit(i)', lambda i: Const('%d' % (i,))),
        ('lit==StrLit(_)', expr_strlit),
        ('TupleLit(es)', expr_tuple_lit))

# STATEMENTS

def write_assert(e, msg):
    ex = express(e)
    pass_ = new_label('pass')
    fail_ = new_label('fail')
    out('br i1 ')
    out_xpr(ex)
    comma()
    out_label_ref(pass_)
    comma()
    out_label_ref(fail_)
    newline()
    out_label(fail_)
    m = express(msg)
    out('call void @fail(i8* %s) noreturn' % (xpr_str(m),))
    newline()
    out('unreachable')
    newline()
    out_label(pass_)

def write_assign(lhs, e):
    ex = express(e)
    out('; TODO %s' % (xpr_str(ex),))

def write_augassign(op, lhs, e):
    ex = express(e)
    out('; TODO %s' % (xpr_str(ex),))

def write_break():
    begin, end = env(LOCALS).loopLabels
    out_br_label(end)

def write_cond(cs, else_):
    n = len(cs)
    haveElse = isJust(else_)
    elif_ = Nothing()
    else_label = Nothing()
    endif = new_label('endif')
    for i, case in enumerate(cs):
        if isJust(elif_):
            out_label(fromJust(elif_))
        ex = express(case.test)
        out('br i1 ')
        out_xpr(ex)
        comma()
        then = new_label('then')
        out_label_ref(then)
        comma()
        if i + 1 < n:
            elif_ = Just(new_label('elif'))
            out_label_ref(elif_)
        elif haveElse:
            e = new_label('else')
            out_label_ref(e)
            else_label = Just(e)
        else:
            out_label_ref(endif)
        newline()
        out_label(then)
        write_body(case.body)
        if i < n - 1 or haveElse:
            out_br_label(endif)
    if haveElse:
        out_label(fromJust(else_label))
        write_body(fromJust(else_))
    out_label(endif)

def has_static_replacement(v, e):
    if has_extrinsic(Replacement, v):
        return True
    m = match(e)
    if m('FuncExpr(f)'):
        f = m.arg
        if has_extrinsic(expand.VarUsage, v):
            if extrinsic(expand.VarUsage, v).isReassigned:
                return False
        add_extrinsic(Replacement, v, Const(func_ref(f)))
        return True
    return False

def write_defn(v, e):
    if has_static_replacement(v, e):
        return
    ex = express(e)
    out_name_reg(v)
    out(' = alloca ')
    t = typeof(e)
    out_t_nospace(t)
    newline()
    out('store ')
    out_t(t)
    out_xpr(ex)
    comma()
    out_t_ptr(t)
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
    ex = express(e)
    # Don't need to output ex since it is discarded and has no side-effects

def write_extrinsic_stmt(extr):
    clear_indent()
    out('; extrinsic ')
    out(extrinsic(Name, extr))

def write_top_func(f, ps, body):
    clear_indent()
    out('define i32 ')
    out_func_ref(f)

    # param temporaries
    out('(')
    first = True
    tmps = []
    for p in ps:
        if first:
            first = False
        else:
            comma()
        out('i32 ')
        tmp = temp_reg_named(extrinsic(Name, p))
        out_xpr(tmp)
        tmps.append(tmp)
    out(')')

    out(' {\nentry:')

    if len(ps) > 0:
        newline()
        # write params to mem
        for p, tmp in zip(ps, tmps):
            out_name_reg(p)
            out(' = alloca i32')
            newline()
            out('store i32 ')
            out_xpr(tmp)
            comma()
            out('i32* ')
            out_name_reg(p)
            newline()
    newline()

    write_body(body)
    clear_indent()
    out('}\n')

def write_return(expr):
    ex = express(expr)
    out('ret i32 ')
    out_xpr(ex)

def write_while(cond, body):
    begin = new_label('loop')
    body_label = new_label('body')
    exit = new_label('exit')

    # for break and continue
    old_labels = env(LOCALS).loopLabels
    env(LOCALS).loopLabels = (begin, exit)

    out_label(begin)
    ex = express(cond)
    out('br i1 ')
    out_xpr(ex)
    comma()
    out_label_ref(body_label)
    comma()
    out_label_ref(exit)
    newline()
    out_label(body_label)
    write_body(body)
    out_br_label(begin)
    out_label(exit)

    env(LOCALS).loopLabels = old_labels

def write_stmt(stmt):
    match(stmt,
        ("Assert(e, m)", write_assert),
        ("Assign(lhs, e)", write_assign),
        ("AugAssign(op, lhs, e)", write_augassign),
        ("Break()", write_break),
        ("Cond(cs, else_)", write_cond),
        ("Defn(v, e)", write_defn),
        ("ExprStmt(e)", write_expr_stmt),
        ("Return(e)", write_return),
        ("While(c, b)", write_while))
    newline()

def write_body(body):
    map_(write_stmt, match(body, ('Body(ss)', identity)))

def write_top_strlit(var, s):
    ir = env(IR)
    add_extrinsic(Name, var, '.LC%d' % (ir.lcCtr,))
    ir.lcCtr += 1

    clear_indent()
    out('%s = internal constant %s' % (global_ref(var), escape_strlit(s)))

def escape_strlit(s):
    b = s.encode('utf-8')
    lit = '[%d x i8] c"' % (len(b) + 1)
    for c in iter(b):
        i = ord(c)
        lit += c if 31 < i < 127 else '\\%02x' % (i,)
    return lit + '\\00"'

def write_top(top):
    match(top,
        ("TopDefn(_, FuncExpr(f==Func(ps, body)))", write_top_func),
        ("TopDefn(v, e)", write_defn),
        ("TopDT(form)", write_dtstmt),
        ("TopExtrinsic(extr)", write_extrinsic_stmt))
    newline()

def write_unit(unit):
    for top in unit.tops:
        if has_extrinsic(expand.Expansion, top):
            for ex in extrinsic(expand.Expansion, top):
                in_env(LOCALS, setup_locals(), lambda: match(ex,
                    ("ExStrLit(var, s)", write_top_strlit),
                    ("ExSurfacedFunc(f==Func(ps, body))", write_top_func)))
                newline()
        in_env(LOCALS, setup_locals(), lambda: write_top(top))

def write_ir(filename, prog):
    in_env(IR, setup_ir(filename),
        lambda: scope_extrinsic(Replacement,
        lambda: write_unit(prog)))

def simple_test():
    add = lambda a, b: symcall('+', [a, b])

    body = []
    func = Func([], Body(body))
    add_extrinsic(Name, func, 'main')
    foo = Var()
    add_extrinsic(Name, foo, 'foo')
    sum = add(Bind(BindVar(foo)), IntLit(1))
    body += [Defn(foo, add(IntLit(40), IntLit(2))),
             Return(sum)]
    write_ir('ir/simple_test.ll', Body([FuncStmt(func)]))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
