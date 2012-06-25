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

EXPORTSYMS = new_env('EXPORTSYMS', bool)

DECLSONLY = new_env('DECLSONLY', bool)

def setup_ir(filename):
    stream = file(filename, 'wb') # really ought to close explicitly
    return IRInfo(stream, 0)

def setup_locals():
    return IRLocals([], False, True, False, 0, Nothing(), {}, Nothing())

Xpr, Reg, Tmp, ConstStruct, Const, ConstOp, ConstCast = ADT('Xpr',
        'Reg', ('label', 'str'), ('index', 'int'),
        'Tmp', ('index', 'int'),
        'ConstStruct', ('vals', ['(IType, Xpr)']),
        'Const', ('frag', 'str'),
        'ConstOp', ('op', 'str'), ('args', ['(IType, Xpr)']),
        'ConstCast', ('kind', str), ('val', 'Xpr'), ('type', 'IType'))

def is_const(x):
    return match(x,
        ('Reg(_, _)', lambda: False), ('Tmp(_)', lambda: False),
        ('ConstStruct(_)', lambda: True),
        ('Const(_)', lambda: True), ('ConstOp(_, _)', lambda: True))

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
            ('IRLabel(lbl)', lambda l: '\n%s:\n' % (label_str(l),)
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
                    ('ConstStruct(vals)', conststruct_str),
                    ('Const(s)', identity),
                    ('ConstOp(f, args)', constop_str))

def constop_str(f, args):
    ss = ('%s %s' % (t_str(t), xpr_str(x)) for t, x in args)
    return '%s (%s)' % (f, ', '.join(ss))

def conststruct_str(vals):
    ss = ('%s %s' % (t_str(t), xpr_str(x)) for t, x in vals)
    return '{ %s }' % (', '.join(ss),)

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
    newline()

def store_xpr(t, val, dest):
    out('store ')
    out_t(t)
    out_xpr(val)
    comma()
    out_t_ptr(t)
    out_xpr(dest)
    newline()

def malloc(t):
    sizeof = temp_reg_named('sizeof')
    out_xpr(sizeof)
    out(' = ptrtoint ')
    out_t_ptr(t)
    out('getelementptr(')
    out_t_ptr(t)
    out('null, i32 1) to i32')
    newline()
    mem = temp_reg()
    out_xpr(mem)
    out(' = call i8* @malloc')
    write_args([(IInt(), sizeof)])
    newline()
    inst = temp_reg_named('inst')
    out_xpr(inst)
    out(' = bitcast i8* ')
    out_xpr(mem)
    out(' to ')
    out_t_nospace(IPtr(t))
    newline()
    return inst

def write_args(args):
    out('(')
    first = True
    for t, arg in args:
        if first:
            first = False
        else:
            comma()
        out_t(t)
        out_xpr(arg)
    out(')')

def get_field_ptr(ex, t, f):
    fieldptr = temp_reg_named(extrinsic(Name, f))
    out_xpr(fieldptr)
    out(' = getelementptr ')
    out_t(t)
    out_xpr(ex)
    comma()
    out('i32 0')
    comma()
    out('i32 %d' % (extrinsic(expand.FieldIndex, f),))
    newline()
    return fieldptr

def build_struct(t, args):
    i = 0
    accum = Const('undef')
    for ft, tmp in args:
        new_val = temp_reg()
        out_xpr(new_val)
        out(' = insertvalue ')
        out_t(t)
        out_xpr(accum)
        comma()
        out_t(ft)
        out_xpr(tmp)
        comma()
        out(str(i))
        newline()
        i += 1
        accum = new_val
    return accum

def cast(xpr, src, dest):
    if types_equal(src, dest):
        return xpr
    s = IVoidPtr() if matches(src, 'IPtr(_)') else src
    d = IVoidPtr() if matches(dest, 'IPtr(_)') else dest
    kind = match((s, d),
        ('(IInt(), IVoidPtr())', lambda: 'inttoptr'),
        ('(IVoidPtr(), IInt(_))', lambda: 'ptrtoint'),
        ('(IVoidPtr(), IVoidPtr())', lambda: 'bitcast'),
        ('_', lambda: 'invalid'))
    assert kind != 'invalid', "Can't cast %s to %s" % (src, dest)
    if is_const(xpr):
        return ConstCast(kind, xpr, dest)
    tmp = temp_reg_named(kind)
    out_xpr(tmp)
    out(' = %s ' % (kind,))
    out_t(src)
    out_xpr(xpr)
    out(' to ')
    out_t_nospace(dest)
    newline()
    return tmp

# TYPES

IType, IInt, IBool, IVoid, ITuple, IData, IFunc, IPtr, IVoidPtr = ADT('IType',
        'IInt',
        'IBool',
        'IVoid',
        'ITuple', ('types', ['IType']),
        'IData', ('datatype', '*DataType'),
        'IFunc', ('params', ['IType']), ('ret', 'IType'),
        'IPtr', ('type', 'IType'),
        'IVoidPtr')

APPS = new_env('APPS', {TypeVar: IType})

def convert_type(t):
    return match(t,
        ("TPrim(PInt())", IInt),
        ("TPrim(PBool())", IBool),
        ("TVoid()", IVoid),
        ("TVar(tvar)", _conv_tvar),
        ("TFunc(ps, r)", lambda ps, r:
                         IFunc(map(convert_type, ps), convert_type(r))),
        ("TData(dt)", lambda dt: IPtr(IData(dt))),
        ("TApply(t, tvar, a)", _conv_apply),
        ("TArray(t)", lambda t: IPtr(convert_type(t))),
        ("TTuple(ts)", lambda ts: IPtr(ITuple(map(convert_type, ts)))))

def _conv_apply(target, tvar, app):
    apps = env(APPS) if have_env(APPS) else {}
    apps[tvar] = in_env(APPS, {}, lambda: convert_type(target))
    return in_env(APPS, apps, lambda: convert_type(target))

def _conv_tvar(tvar):
    if have_env(APPS):
        return env(APPS).get(tvar, IVoidPtr())
    return IVoidPtr()

def types_equal(src, dest):
    same = lambda: True
    return match((src, dest),
        ('(IInt(), IInt())', same),
        ('(IBool(), IBool())', same),
        ('(IVoid(), IVoid())', same),
        ('(IData(a), IData(b))', lambda a, b: a is b),
        ('(IFunc(ps1, r1), IFunc(ps2, r2))', lambda ps1, r1, ps2, r2:
            len(ps1) == len(ps2) and
            all(types_equal(a, b) for a, b in zip(ps1, ps2)) and
            types_equal(r1, r2)),
        ('(IPtr(a), IPtr(b))', types_equal),
        ('(IVoidPtr(), IVoidPtr())', same),
        ('_', lambda: False))

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
        ("ITuple(ts)", lambda ts: "{%s}" % (', '.join(map(t_str, ts)))),
        ("IData(dt)", lambda dt: "%%%s" % extrinsic(Name, dt)),
        ("IFunc(ps, r)", t_func_str),
        ("IPtr(p)", lambda p: t_str(p) + "*"),
        ("IVoidPtr()", lambda: "i8*"))

def t_func_str(ps, r):
    return '%s (%s)' % (', '.join(t_str(p) for p in ps), t_str(r))

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
        ('key("negate")', lambda: 'negate'),
        ('_', lambda: ''))

def bin_op(b):
    # grr boilerplate
    return match(b,
        ('key("+")', lambda: 'add'), ('key("-")', lambda: 'sub'),
        ('key("*")', lambda: 'mul'), ('key("//")', lambda: 'sdiv'),
        ('key("%")', lambda: 'srem'),
        ('key("&")', lambda: 'and'), ('key("|")', lambda: 'or'),
        ('key("^")', lambda: 'xor'),
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
    assert op == 'not' or op == 'negate'
    pivot = Const('1' if op == 'not' else '0')
    if is_const(arg):
        return ConstOp('sub', [(t, pivot), (t, arg)])
    else:
        tmp = temp_reg_named(op)
        out_xpr(tmp)
        out(' = sub ')
        out_t(t)
        out_xpr(pivot)
        comma()
        out_xpr(arg)
        newline()
        return tmp

def expr_binop(op, left, right, t):
    if is_const(left) and is_const(right):
        return ConstOp(op, [(t, left), (t, right)])
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
    paramts = match(typeof(f), ("IFunc(paramts, _)", identity))
    argxs = []
    for arg, paramt in zip(args, paramts):
        argt = typeof(arg)
        argx = cast(express(arg), argt, paramt)
        argxs.append((argt, argx))

    out_xpr(tmp)
    out(' = call ')
    out_t(t)
    out_xpr(fx)
    write_args(argxs)
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

def expr_func(f, ps, body):
    clos = extrinsic(expand.Closure, f)
    assert not clos.isClosure, "TODO"
    return Const(func_ref(clos.func))

def expr_match(m, e, cs):
    return Const('undef ;match')
    #for c in cs:
    #cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))

def expr_attr(e, f):
    ex = express(e)
    fieldptr = get_field_ptr(ex, typeof(e), f)
    val = temp_reg_named(extrinsic(Name, f))
    out_xpr(val)
    out(' = load ')
    out_t_ptr(convert_type(f.type))
    out_xpr(fieldptr)
    newline()
    return val

def expr_strlit(lit):
    info = extrinsic(expand.ExpandedDecl, lit)
    tmp = temp_reg()
    out_xpr(tmp)
    out(' = getelementptr [%d x i8]* %s, i32 0, i32 0' %
            (extrinsic(LiteralSize, info.var), global_ref(info.var)))
    newline()
    return tmp

def expr_tuple_lit(lit, ts):
    tt = match(typeof(lit), ("IPtr(tt==ITuple(_))", identity))
    tmp = malloc(tt)
    xs = [(typeof(t), express(t)) for t in ts]
    struct = build_struct(tt, xs)
    store_xpr(tt, struct, tmp)
    return tmp

def express(expr):
    return match(expr,
        ('And(l, r)', expr_and),
        ('Bind(BindBuiltin(b))', expr_bind_builtin),
        ('Bind(BindCtor(c))', expr_bind_ctor),
        ('Bind(BindVar(v))', expr_bind_var),
        ('e==Call(f, args)', expr_call),
        ('FuncExpr(f==Func(ps, body))', expr_func),
        ('m==Match(p, cs)', expr_match),
        ('Attr(e, f)', expr_attr),
        ('Or(l, r)', expr_or),
        ('IntLit(i)', lambda i: Const('%d' % (i,))),
        ('lit==StrLit(_)', expr_strlit),
        ('Ternary(c, l, r)', expr_ternary),
        ('lit==TupleLit(es)', expr_tuple_lit))

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

def store_attr(dest, f, val):
    ex = express(dest)
    fieldptr = get_field_ptr(ex, typeof(dest), f)
    store_xpr(convert_type(f.type), val, fieldptr)

def store_lhs(lhs, x):
    match(lhs,
        ('LhsVar(v)', lambda v: store_var(v, x)),
        ('LhsAttr(e, f)', lambda e, f: store_attr(e, f, x)))

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

def write_field_specs(fields, discrim):
    verbose = not env(DECLSONLY)
    if verbose:
        out('{')
        newline()
    else:
        out('{ ')

    if discrim:
        ix = Field(TInt())
        add_extrinsic(Name, ix, "discrim")
        fields = [ix] + fields

    n = len(fields)
    for i, f in enumerate(fields):
        out_t_nospace(convert_type(f.type))
        if i < n - 1:
            comma()
        elif verbose:
            out('  ')
        if verbose:
            out('; %s' % (extrinsic(Name, f),))
            newline()
    if verbose:
        clear_indent()
        out('}')
    else:
        out(' }')

def write_ctor(ctor, dt, discrim):
    dtt = IData(dt)
    inst = temp_reg_named(extrinsic(Name, dt))

    clear_indent()
    out('declare ' if env(DECLSONLY) else 'define ')
    out_t_ptr(dtt)
    out_func_ref(ctor)
    fts = [convert_type(f.type) for f in ctor.fields]
    if env(DECLSONLY):
        write_param_types(fts)
        newline()
        return
    tmps = write_params(ctor.fields, fts)
    out(' {')
    newline()

    ctort = IData(ctor)
    inst = malloc(ctort)

    if discrim:
        fts = [IInt()] + fts
        tmps = [Const(str(extrinsic(expand.CtorIndex, ctor)))] + tmps
    assert len(fts) == len(tmps)
    struct = build_struct(ctort, zip(fts, tmps))
    store_xpr(ctort, struct, inst)

    ret = inst
    if discrim:
        ret = cast(ret, IPtr(ctort), IPtr(dtt))
    out('ret ')
    out_t_ptr(dtt)
    out_xpr(ret)
    newline()
    clear_indent()
    out('}')
    newline()

def write_dtstmt(form):
    discrim = len(form.ctors) > 1
    if discrim:
        clear_indent()
        out_name_reg(form)
        out(' = type opaque')
        newline()
    for ctor in form.ctors:
        clear_indent()
        out_name_reg(ctor)
        out(' = type ')
        write_field_specs(ctor.fields, discrim)
        newline()
        write_ctor(ctor, form, discrim)
    if not env(DECLSONLY):
        clear_indent()
        newline()

def write_expr_stmt(e):
    ex = express(e)
    # Don't need to output ex since it is discarded and has no side-effects

def write_extrinsic_stmt(extr):
    clear_indent()
    out('; extrinsic ')
    out(extrinsic(Name, extr))
    newline()

def write_param_types(tps):
    out('(')
    first = True
    for t in tps:
        if first:
            first = False
        else:
            comma()
        out_t_nospace(t)
    out(')')

def write_params(ps, tps):
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
    out(')')
    return tmps

def write_top_func(f, ps, body):
    tps, tret = match(extrinsic(TypeOf, f),
        ('TFunc(p, r)', lambda p, r: (map(convert_type, p), convert_type(r))))
    assert len(ps) == len(tps)

    clear_indent()
    if env(DECLSONLY):
        out('declare ')
    else:
        out('define ')
        if not env(EXPORTSYMS):
            out('internal ')
    out_t(tret)
    out_func_ref(f)
    if env(DECLSONLY):
        write_param_types(tps)
        newline()
        return
    tmps = write_params(ps, tps)
    out(' {')
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

    write_body(body)

    # Clean up, discard unused pending block if any
    lcl = env(LOCALS)
    if isJust(lcl.pendingBlock):
        last_block = fromJust(lcl.pendingBlock)
        if last_block.label.used:
            out('ret void')
            term()
    lcl.chunks.append(IRStr('}\n\n'))

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

def write_body(body):
    map_(write_stmt, match(body, ('Body(ss)', identity)))

def write_top_var_func(v, f):
    if not env(DECLSONLY):
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
    newline()

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

def as_local(f):
    lcl = setup_locals()
    in_env(LOCALS, lcl, f)
    flush(lcl)

def write_unit(unit):
    for top in unit.tops:
        if has_extrinsic(expand.Expansion, top):
            for ex in extrinsic(expand.Expansion, top):
                in_env(EXPORTSYMS, False, lambda: as_local(lambda: match(ex,
                    ("ExStrLit(var, s)", write_top_strlit),
                    ("ExSurfacedFunc(f==Func(ps, body))", write_top_func))))
            newline()
        in_env(EXPORTSYMS, True, lambda: as_local(lambda: write_top(top)))

def write_unit_decls(unit):
    for top in unit.tops:
        as_local(lambda: write_top(top))

prelude = """; prelude
%Type = type opaque
declare i8* @malloc(i32)
declare void @fail(i8*) noreturn

"""

def write_imports(dep):
    dt = match(dep.rootType, ('TData(dt)', identity))
    if dt is DATATYPES['CompilationUnit'].__form__:
        imm_out('; %s' % (extrinsic(Name, dep),))
        newline()
        in_env(DECLSONLY, True, lambda: write_unit_decls(dep.root))

LLFile = new_extrinsic('LLFile', str)
OFile = new_extrinsic('OFile', str)

def write_ir(mod):
    filename = 'ir/' + extrinsic(Filename, mod) + '.ll'

    def go():
        imm_out(prelude)
        walk_deps(write_imports, mod)
        newline()
        imm_out('; main')
        newline()
        in_env(DECLSONLY, False, lambda: write_unit(mod.root))

    in_env(IR, setup_ir(filename),
        lambda: scope_extrinsic(Replacement,
        lambda: scope_extrinsic(LiteralSize,
        go)))

    add_extrinsic(LLFile, mod, filename)

def compile(mod):
    ll = extrinsic(LLFile, mod)
    s = ll + '.s'
    o = ll + '.o'
    if os.system('llc -disable-cfi -o %s %s' % (s, ll)) != 0:
        return False
    if os.system('cc -c -o %s %s' % (o, s)) != 0:
        return False
    add_extrinsic(OFile, mod, o)
    return True

def link(mod):
    objs = ['ir/z.o']

    def add_obj(dep):
        dt = dep.rootType.data
        if dt is DATATYPES['CompilationUnit'].__form__:
            if not has_extrinsic(OFile, dep):
                print col('Yellow', 'omitting missing'), extrinsic(Name, dep)
                return
            objs.append(extrinsic(OFile, dep))
    walk_deps(add_obj, mod)

    objs.append(extrinsic(OFile, mod))
    binary = 'bin/%s' % (extrinsic(Filename, mod),)
    return os.system('cc -o %s %s' % (binary, ' '.join(objs))) == 0

def in_llvm_env(func):
    captures = {}
    extrs = [LLFile, OFile]
    return capture_scoped(extrs, captures, func)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
