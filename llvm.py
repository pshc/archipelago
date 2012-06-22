from atom import *
import expand
import os
import sys

Label = DT('Label', ('name', str),
                    ('index', int),
                    ('used', bool),
                    ('replacedBy', 'Maybe(Label)'))

IRChunk, IRStr, IRLabel, IRLabelRef = ADT('IRChunk',
        'IRStr', ('str', str),
        'IRLabel', ('label', '*Label'),
        'IRLabelRef', ('label', '*Label'), ('naked', bool))

IRInfo = DT('IRInfo', ('stream', None),
                      ('lcCtr', int))
IR = new_env('IR', IRInfo)

IRBlock = DT('IRBlock', ('label', Label), ('needsJumpInto', bool))

IRLocals = DT('IRLocals', ('chunks', [IRChunk]),
                          ('needIndent', bool),
                          ('needTerminator', bool),
                          ('unreachable', bool),
                          ('tempCtr', int),
                          ('pendingBlock', 'Maybe(IRBlock)'),
                          ('labelCtrs', {str: int}),
                          ('loopLabels', 'Maybe((Label, Label))'))

LOCALS = new_env('LOCALS', IRLocals)

EXPORT = new_env('EXPORT', bool)

def setup_ir(filename):
    stream = file(filename, 'wb') # really ought to close explicitly
    return IRInfo(stream, 0)

def setup_locals():
    return IRLocals([], False, True, False, 0, Nothing(), {}, Nothing())

Xpr, Reg, Tmp, Const, ConstOp = ADT('Xpr',
        'Reg', ('label', 'str'), ('index', 'int'),
        'Tmp', ('index', 'int'),
        'Const', ('frag', 'str'),
        'ConstOp', ('op', 'str'), ('args', ['Xpr']), ('type', 'IType'))

def is_const(x):
    return match(x,
        ('Reg(_, _)', lambda: False), ('Tmp(_)', lambda: False),
        ('Const(_)', lambda: True), ('ConstOp(_, _, _)', lambda: True))

Replacement = new_extrinsic('Replacement', Xpr)

LiteralSize = new_extrinsic('LiteralSize', int)

# OUTPUT

def imm_out(s):
    env(IR).stream.write(s)
    if not env(GENOPTS).quiet:
        sys.stdout.write(s)

def flush(lcl):
    def label_str(label):
        label = collapse_label_indirection(label)
        # Unique labels don't need an index
        if label.index == 0 and lcl.labelCtrs[label.name] == 1:
            return label.name
        else:
            return '%s_%d' % (label.name, label.index)
    chunks = lcl.chunks
    lcl.chunks = []
    for chunk in chunks:
        imm_out(match(chunk,
            ('IRStr(s)', identity),
            ('IRLabel(lbl)', lambda l: '%s:\n' % (label_str(l),)
                                       if l.used else ''),
            ('IRLabelRef(l, True)', lambda l: '%%%s' % (label_str(l),)),
            ('IRLabelRef(l, False)', lambda l: 'label %%%s' % (label_str(l),))
        ))

def out(s):
    lcl = env(LOCALS)
    if lcl.unreachable:
        return
    if isJust(lcl.pendingBlock):
        block = fromJust(lcl.pendingBlock)
        if block.needsJumpInto:
            # Blocks can't implicitly fall-through to the next block, so jump
            ref = IRLabelRef(block.label, False)
            block.label.used = True
            lcl.chunks += [IRStr('  br '), ref, IRStr('\n')]
        lcl.chunks.append(IRLabel(block.label))
        lcl.pendingBlock = Nothing()
    if lcl.needIndent:
        lcl.chunks.append(IRStr('  %s' % (s,)))
        clear_indent()
    else:
        lcl.chunks.append(IRStr(s))

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
    lcl = env(LOCALS)
    # Empty label substitution
    if isJust(lcl.pendingBlock):
        fromJust(lcl.pendingBlock).label.replacedBy = Just(label)
    lcl.pendingBlock = Just(IRBlock(label, lcl.needTerminator))
    lcl.needIndent = True
    lcl.needTerminator = True
    lcl.unreachable = False

def out_naked_label_ref(label, naked):
    lcl = env(LOCALS)
    assert isNothing(lcl.pendingBlock), "Unexpected label ref after label"
    if not lcl.unreachable:
        lcl.chunks.append(IRLabelRef(label, naked))
        label.used = True

def out_label_ref(label):
    out_naked_label_ref(label, False)

def out_xpr(x):
    out(xpr_str(x))

def xpr_str(x):
    return match(x, ('Reg(nm, i)', lambda nm, i: '%%%s.%d' % (nm, i)),
                    ('Tmp(i)', lambda i: '%%.%d' % (i,)),
                    ('Const(s)', identity),
                    ('ConstOp(f, args, t)', constop_str))

def constop_str(f, args, t):
    ts = t_str(t)
    return '%s (%s)' % (f, ', '.join('%s %s' % (ts, xpr_str(r)) for r in args))

def clear_indent():
    env(LOCALS).needIndent = False

def newline():
    if have_env(LOCALS):
        if isJust(env(LOCALS).pendingBlock):
            return
        out('\n')
        env(LOCALS).needIndent = True
    else:
        imm_out('\n')

def term():
    env(LOCALS).needTerminator = False
    newline()
    env(LOCALS).unreachable = True

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
    ctr = lcl.labelCtrs.get(nm, 0)
    label = Label(nm, ctr, False, Nothing())
    lcl.labelCtrs[nm] = ctr + 1
    return label

def collapse_label_indirection(label):
    if isNothing(label.replacedBy):
        return label
    indirect = []
    prev = label
    label = fromJust(label.replacedBy)
    while isJust(label.replacedBy):
        label = fromJust(label.replacedBy)
        indirect.append(prev)
        prev = label
    for i in indirect:
        i.replacedBy = Just(label)
    return label

# INSTRUCTIONS

def br(label):
    out('br ')
    out_label_ref(label)
    term()

def br_cond(cond, true, false):
    out('br i1 ')
    out_xpr(cond)
    comma()
    out_label_ref(true)
    comma()
    out_label_ref(false)
    term()

def phi2(reg, t, e1, lbl1, e2, lbl2):
    out_xpr(reg)
    out(' = phi ')
    out_t(t)
    out('[ ')
    out_xpr(e1)
    comma()
    out_naked_label_ref(lbl1, True)
    out(' ]')
    comma()
    out('[ ')
    out_xpr(e2)
    comma()
    out_naked_label_ref(lbl2, True)
    out(' ]')
    newline()

def store_named(t, xpr, named):
    out('store ')
    out_t(t)
    out_xpr(xpr)
    comma()
    out_t_ptr(t)
    out_name_reg(named)

def store_xpr(t, val, dest):
    out('store ')
    out_t(t)
    out_xpr(val)
    comma()
    out_t_ptr(t)
    out_xpr(dest)

# TYPES

IType, IInt, IBool, IVoid, IData, IPtr, IVoidPtr = ADT('IType',
        'IInt',
        'IBool',
        'IVoid',
        'IData', ('datatype', '*DataType'),
        'IPtr', ('type', 'IType'),
        'IVoidPtr')

def convert_type(t):
    return match(t,
        ("TPrim(PInt())", lambda: IInt()),
        ("TPrim(PBool())", lambda: IBool()),
        ("TVoid()", lambda: IVoid()),
        ("TVar(_)", lambda: IVoidPtr()),
        ("TFunc(_, _)", lambda: IVoidPtr()),
        ("TData(dt)", IData),
        ("TApply(_, _, _)", lambda: IVoidPtr()),
        ("TArray(t)", lambda t: IPtr(convert_type(t))),
        ("TTuple(_)", lambda: IVoidPtr()))

def typeof(e):
    if has_extrinsic(TypeOf, e):
        return convert_type(extrinsic(TypeOf, e))
    def no_type():
        assert isinstance(e, Expr), "%s is not expr" % (e,)
        print 'HAS NO TYPEOF: %s' % (e,)
        return IInt()
    return match(e,
        ("IntLit(_)", lambda: IInt()),
        ("_", no_type))

def t_str(t):
    return match(t,
        ("IInt()", lambda: "i32"),
        ("IBool()", lambda: "i1"),
        ("IVoid()", lambda: "void"),
        ("IData(dt)", lambda dt: "%%%s*" % extrinsic(Name, dt)),
        ("IPtr(p)", lambda p: t_str(p) + "*"),
        ("IVoidPtr()", lambda: "i8*"))

def out_t(t):
    out('%s ' % (t_str(t),))
def out_t_ptr(t):
    out('%s* ' % (t_str(t),))
def out_t_nospace(t):
    out(t_str(t))

# EXPRESSIONS

def expr_and(l, r):
    entry = new_label('and')
    out_label(entry)
    left = express(l)
    both = new_label('both')
    end = new_label('endand')
    br_cond(left, both, end)
    # left was true
    out_label(both)
    right = express(r)
    br(end)
    # short-circuit with phi
    out_label(end)
    truth = temp_reg_named('and')
    phi2(truth, IBool(), right, both, Const('false'), entry)
    return truth

def expr_or(l, r):
    entry = new_label('or')
    out_label(entry)
    left = express(l)
    both = new_label('both')
    end = new_label('endor')
    br_cond(left, end, both)
    # left was false
    out_label(both)
    right = express(r)
    br(end)
    # short-circuit with phi
    out_label(end)
    truth = temp_reg_named('or')
    phi2(truth, IBool(), right, both, Const('true'), entry)
    return truth

def expr_ternary(c, t, f):
    cond = express(c)
    yes = new_label('yes')
    no = new_label('no')
    end = new_label('endternary')
    br_cond(cond, yes, no)

    out_label(yes)
    true = express(t)
    br(end)

    out_label(no)
    false = express(f)
    br(end)

    out_label(end)
    result = temp_reg_named('either')
    phi2(result, typeof(t), true, yes, false, no)
    return result

def expr_bind_builtin(b):
    return match(b,
        ('key("True")', lambda: Const('true')),
        ('key("False")', lambda: Const('false')))

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

def una_op(b):
    # grr boilerplate
    return match(b,
        ('key("not")', lambda: 'not'),
        ('_', lambda: ''))

def bin_op(b):
    # grr boilerplate
    return match(b,
        ('key("+")', lambda: 'add'),
        ('key("-")', lambda: 'sub'),
        ('key("*")', lambda: 'mul'),
        ('key("==")', lambda: 'icmp eq'), ('key("!=")', lambda: 'icmp ne'),
        ('key("<")', lambda: 'icmp slt'), ('key(">")', lambda: 'icmp sgt'))

def aug_op(b):
    return match(b,
        ('AugAdd()', lambda: 'add'),
        ('AugSubtract()', lambda: 'sub'),
        ('AugMultiply()', lambda: 'mul'),
        ('AugDivide()', lambda: 'sdiv'), # or udiv...
        ('AugModulo()', lambda: 'srem')) # or urem...

def expr_unary(op, arg, t):
    assert op == 'not'
    assert matches(t, 'IBool()')
    if is_const(arg):
        return ConstOp('sub', [Const(1), arg], t)
    else:
        tmp = temp_reg_named(op)
        out_xpr(tmp)
        out(' = sub i1 1')
        comma()
        out_xpr(arg)
        newline()
        return tmp

def expr_binop(op, left, right, t):
    if is_const(left) and is_const(right):
        return ConstOp(op, [left, right], t)
    else:
        tmp = temp_reg_named(op.split(' ')[-1])
        out_xpr(tmp)
        out(' = %s ' % (op,))
        out_t(t)
        out_xpr(left)
        comma()
        out_xpr(right)
        newline()
        return tmp

def write_call(tmp, f, args, t):
    fx = express(f)
    argxs = [(express(arg), typeof(arg)) for arg in args]
    out_xpr(tmp)
    out(' = call ')
    out_t(t)
    out_xpr(fx)
    write_xpr_list(argxs)
    newline()

def expr_call(e, f, args):
    t = typeof(e)
    m = match(f)
    if m('Bind(BindBuiltin(b))'):
        b = m.arg
        op = una_op(b)
        if op != '':
            assert len(args) == 1, '%s is unary' % (op,)
            arg = express(args[0])
            m.ret(expr_unary(op, arg, typeof(args[0])))
        else:
            op = bin_op(b)
            assert len(args) == 2, '%s requires two args' % (op,)
            left = express(args[0])
            right = express(args[1])
            m.ret(expr_binop(op, left, right, typeof(args[0])))
    elif m('Bind(BindVar(v))'):
        v = m.arg
        tmp = temp_reg_named(extrinsic(Name, v))
        write_call(tmp, f, args, t)
        m.ret(tmp)
    else:
        tmp = temp_reg()
        write_call(tmp, f, args, t)
        m.ret(tmp)
    return m.result()

def write_xpr_list(args):
    out('(')
    first = True
    for arg, t in args:
        if first:
            first = False
        else:
            comma()
        out_t(t)
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
    out(' = getelementptr [%d x i8]* %s, i32 0, i32 0' %
            (extrinsic(LiteralSize, info.var), global_ref(info.var)))
    newline()
    return tmp

def expr_tuple_lit(ts):
    xs = ['%s %s' % (t_str(typeof(t)), xpr_str(express(t))) for t in ts]
    return Const('{ %s }' % (', '.join(xs),))

def express(expr):
    return match(expr,
        ('And(l, r)', expr_and),
        ('Bind(BindBuiltin(b))', expr_bind_builtin),
        ('Bind(BindCtor(c))', expr_bind_ctor),
        ('Bind(BindVar(v))', expr_bind_var),
        ('e==Call(f, args)', expr_call),
        ('FuncExpr(f==Func(ps, body))', expr_func),
        ('m==Match(p, cs)', expr_match),
        ('Or(l, r)', expr_or),
        ('IntLit(i)', lambda i: Const('%d' % (i,))),
        ('lit==StrLit(_)', expr_strlit),
        ('Ternary(c, l, r)', expr_ternary),
        ('TupleLit(es)', expr_tuple_lit))

# STATEMENTS

def write_assert(e, msg):
    ex = express(e)
    pass_ = new_label('pass')
    fail_ = new_label('fail')
    br_cond(ex, pass_, fail_)
    out_label(fail_)
    m = express(msg)
    out('call void @fail(i8* %s) noreturn' % (xpr_str(m),))
    newline()
    out('unreachable')
    term()
    out_label(pass_)

def store_var(v, xpr):
    store_named(typeof(v), xpr, v)

def store_lhs(lhs, x):
    match(lhs,
        ('LhsVar(v)', lambda v: store_var(v, x)))

def load_lhs(lhs):
    return match(lhs,
        ('LhsVar(v)', expr_bind_var))

def write_assign(lhs, e):
    ex = express(e)
    store_lhs(lhs, ex)

def write_augassign(op, lhs, e):
    right = express(e)
    left = load_lhs(lhs)
    ex = expr_binop(aug_op(op), left, right, typeof(e))
    store_lhs(lhs, ex)

def write_break():
    begin, end = env(LOCALS).loopLabels
    br(end)

def write_continue():
    begin, end = env(LOCALS).loopLabels
    br(begin)

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
        then = new_label('then')
        e = endif
        if i + 1 < n:
            e = new_label('elif')
            elif_ = Just(e)
        elif haveElse:
            e = new_label('else')
            else_label = Just(e)
        br_cond(ex, then, e)
        out_label(then)
        write_body(case.body)
        if i < n - 1 or haveElse:
            br(endif)
    if haveElse:
        out_label(fromJust(else_label))
        write_body(fromJust(else_))
    out_label(endif)

def check_static_replacement(v, f):
    if has_extrinsic(Replacement, v):
        return True
    if has_extrinsic(expand.VarUsage, v):
        if extrinsic(expand.VarUsage, v).isReassigned:
            return False
    add_extrinsic(Replacement, v, Const(func_ref(f)))
    return True

def write_func_defn(v, e, f):
    if not check_static_replacement(v, f):
        write_defn(v, e)

def write_defn(v, e):
    ex = express(e)
    out_name_reg(v)
    out(' = alloca ')
    t = typeof(e)
    out_t_nospace(t)
    newline()
    store_named(t, ex, v)

def write_field_specs(fields):
    out('{ ')
    first = True
    for f in fields:
        if not first:
            comma()
        else:
            first = False
        out_t(convert_type(f.type))
        out(extrinsic(Name, f))
    out(' }')

def write_dtstmt(form):
    if len(form.ctors) > 1:
        for ctor in form.ctors:
            clear_indent()
            out_name_reg(ctor)
            out(' = type ')
            write_field_specs(ctor.fields)
            newline()
        clear_indent()
        out('; skipping %')
        out_name_reg(form)
    else:
        clear_indent()
        out_name_reg(form)
        out(' = type ')
        write_field_specs(form.ctors[0].fields)

def write_expr_stmt(e):
    ex = express(e)
    # Don't need to output ex since it is discarded and has no side-effects

def write_extrinsic_stmt(extr):
    clear_indent()
    out('; extrinsic ')
    out(extrinsic(Name, extr))

def write_top_func(f, ps, body):
    tps, tret = match(extrinsic(TypeOf, f),
        ('TFunc(p, r)', lambda p, r: (map(convert_type, p), convert_type(r))))
    assert len(ps) == len(tps)

    clear_indent()
    out('define ')
    if not env(EXPORT):
        out('internal ')
    out_t(tret)
    out_func_ref(f)

    # param temporaries
    out('(')
    first = True
    tmps = []
    for p, tp in zip(ps, tps):
        if first:
            first = False
        else:
            comma()
        out_t(tp)
        tmp = temp_reg_named(extrinsic(Name, p))
        out_xpr(tmp)
        tmps.append(tmp)
    out(') {')
    newline()

    if len(ps) > 0:
        # write params to mem
        for p, tmp, tp in zip(ps, tmps, tps):
            out_name_reg(p)
            out(' = alloca ')
            out_t(tp)
            newline()
            store_named(tp, tmp, p)
            newline()
        newline()

    write_body(body)

    # Clean up, discard unused pending block if any
    lcl = env(LOCALS)
    if isJust(lcl.pendingBlock):
        last_block = fromJust(lcl.pendingBlock)
        if last_block.label.used:
            out('ret void')
            term()
    lcl.chunks.append(IRStr('}\n'))

def write_return(expr):
    ex = express(expr)
    out('ret ')
    out_t(typeof(expr))
    out_xpr(ex)
    term()

def write_while(cond, body):
    begin = new_label('loop')
    body_label = new_label('body')
    exit = new_label('exit')

    # for break and continue
    old_labels = env(LOCALS).loopLabels
    env(LOCALS).loopLabels = (begin, exit)

    out_label(begin)
    ex = express(cond)
    br_cond(ex, body_label, exit)
    out_label(body_label)
    write_body(body)
    br(begin)
    out_label(exit)

    env(LOCALS).loopLabels = old_labels

def write_stmt(stmt):
    match(stmt,
        ("Assert(e, m)", write_assert),
        ("Assign(lhs, e)", write_assign),
        ("AugAssign(op, lhs, e)", write_augassign),
        ("Break()", write_break),
        ("Continue()", write_continue),
        ("Cond(cs, else_)", write_cond),
        ("Defn(v, e==FuncExpr(f))", write_func_defn),
        ("Defn(v, e)", write_defn),
        ("ExprStmt(e)", write_expr_stmt),
        ("Return(e)", write_return),
        ("While(c, b)", write_while))
    newline()

def write_body(body):
    map_(write_stmt, match(body, ('Body(ss)', identity)))

def write_top_var_func(v, f):
    check_static_replacement(v, f)
    write_top_func(f, f.params, f.body)

def write_top_strlit(var, s):
    ir = env(IR)
    add_extrinsic(Name, var, '.LC%d' % (ir.lcCtr,))
    ir.lcCtr += 1

    clear_indent()
    escaped, n = escape_strlit(s)
    add_extrinsic(LiteralSize, var, n)
    out('%s = internal constant %s' % (global_ref(var), escaped))

def escape_strlit(s):
    b = s.encode('utf-8')
    n = len(b) + 1
    lit = '[%d x i8] c"' % (n,)
    for c in iter(b):
        i = ord(c)
        lit += c if 31 < i < 127 else '\\%02x' % (i,)
    return (lit + '\\00"', n)

def write_top(top):
    match(top,
        ("TopDefn(v, FuncExpr(f))", write_top_var_func),
        ("TopDefn(v, e)", write_defn),
        ("TopDT(form)", write_dtstmt),
        ("TopExtrinsic(extr)", write_extrinsic_stmt))
    newline()

def as_local(f):
    lcl = setup_locals()
    in_env(LOCALS, lcl, f)
    flush(lcl)

prelude = """
declare void @fail(i8*) noreturn

"""

def write_unit(unit):
    imm_out(prelude)
    for top in unit.tops:
        if has_extrinsic(expand.Expansion, top):
            for ex in extrinsic(expand.Expansion, top):
                in_env(EXPORT, False, lambda: as_local(lambda: match(ex,
                    ("ExStrLit(var, s)", write_top_strlit),
                    ("ExSurfacedFunc(f==Func(ps, body))", write_top_func))))
                newline()
        in_env(EXPORT, True, lambda: as_local(lambda: write_top(top)))

def write_ir(filename, prog):
    in_env(IR, setup_ir(filename),
        lambda: scope_extrinsic(Replacement,
        lambda: scope_extrinsic(LiteralSize,
        lambda: write_unit(prog))))

def compile(ll, binary):
    bc = ll + '.bc'
    s = ll + '.s'
    if os.system('llvm-as < %s | opt -mem2reg > %s' % (ll, bc)) != 0:
        return False
    if os.system('llc -disable-cfi -o %s %s' % (s, bc)) != 0:
        return False
    if os.system('cc -o %s ir/z.o %s' % (binary, s)) != 0:
        return False
    return True

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
