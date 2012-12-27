from atom import *
from quilt import *
import expand
import os
import sys

IR = new_env('IR', file)

IRLocals = DT('IRLocals', ('needIndent', bool),
                          ('tempCtr', int))

LOCALS = new_env('LOCALS', IRLocals)

EXPORTSYMS = new_env('EXPORTSYMS', bool)

DECLSONLY = new_env('DECLSONLY', bool)

TypedXpr = DT('TypedXpr', ('type', IType), ('xpr', 'Xpr'))

XprKeyword, KNull, KZeroInitializer, KUndef, KTrue, KFalse = ADT('XKeyword',
    'KNull', 'KZeroInitializer', 'KUndef', 'KTrue', 'KFalse')

Xpr, Reg, Tmp, Global, ConstStruct, ConstInt, ConstFloat, ConstKeyword, \
        ConstOp, ConstCast, \
    ConstElementPtr = ADT('Xpr',
        'Reg', ('label', 'str'),
        'Tmp', ('index', 'int'),
        'Global', ('name', str),
        'ConstStruct', ('vals', [TypedXpr]),
        'ConstInt', ('val', 'int'),
        'ConstFloat', ('val', 'float'),
        'ConstKeyword', ('keyword', XprKeyword),
        'ConstOp', ('op', 'str'), ('args', [TypedXpr]),
        'ConstCast', ('kind', str), ('src', TypedXpr), ('dest', IType),
        'ConstElementPtr', ('src', TypedXpr), ('indexes', [int]))

def is_const(x):
    return match(x,
        ('Reg(_)', lambda: False), ('Tmp(_)', lambda: False),
        ('Global(_)', lambda: True), ('ConstStruct(_)', lambda: True),
        ('ConstInt(_)', lambda: True), ('ConstFloat(_)', lambda: True),
        ('ConstKeyword(_)', lambda: True), ('ConstOp(_, _)', lambda: True),
        ('ConstCast(_, _, _)', lambda: True),
        ('ConstElementPtr(_, _)', lambda: True))

LiteralSize = new_extrinsic('LiteralSize', int)

LocalReg = new_extrinsic('LocalReg', Xpr)

# GLOBAL OUTPUT

def imm_out(s):
    env(IR).write(s)
    if env(GENOPTS).dumpSource:
        sys.stdout.write(s)

def out(s):
    if have_env(LOCALS) and env(LOCALS).needIndent:
        imm_out('  %s' % (s,))
        clear_indent()
    else:
        imm_out(s)

def global_symbol_str(var):
    return extrinsic(expand.GlobalSymbol, var).symbol

def global_symbol(var):
    return Global(global_symbol_str(var))

def out_global_symbol(var):
    out_xpr(global_symbol(var))

def newline():
    if have_env(LOCALS):
        imm_out('\n')
        env(LOCALS).needIndent = True
    else:
        out('\n')

def comma():
    out(', ')

def out_comment(s):
    assert '\n' not in s
    out('; %s' % (s,))
    newline()

# FUNCTION-LOCAL OUTPUT

def out_pretty(a, t):
    out_comment(stringify(a, t))

def out_block_ref(block):
    out('label %%%s' % (block.label,))

def out_xpr(x):
    out(xpr_str(x))

def xpr_str(x):
    return match(x, ('Reg(nm)', lambda nm: '%%%s' % (nm,)),
                    ('Tmp(i)', lambda i: '%%.%d' % (i,)),
                    ('Global(name)', lambda name: '@%s' % (name,)),
                    ('ConstStruct(vals)', conststruct_str),
                    ('ConstInt(i)', str),
                    ('ConstFloat(f)', str),
                    ('ConstKeyword(k)', constkeyword_str),
                    ('ConstOp(f, args)', constop_str),
                    ('ConstCast(kind, src, dest)', constcast_str),
                    ('ConstElementPtr(src, ixs)', constelemptr_str))

def txpr_str(txpr):
    return '%s %s' % (t_str(txpr.type), xpr_str(txpr.xpr))

def constkeyword_str(k):
    return match(k, ('KNull()', lambda: 'null'),
                    ('KZeroInitializer()', lambda: 'zeroinitializer'),
                    ('KUndef()', lambda: 'undef'),
                    ('KTrue()', lambda: 'true'), ('KFalse()', lambda: 'false'))

def constop_str(f, args):
    return '%s (%s)' % (f, ', '.join(map(txpr_str, args)))

def conststruct_str(vals):
    return '{ %s }' % (', '.join(map(txpr_str, vals)),)

def constcast_str(kind, src, dest):
    return '%s (%s to %s)' % (kind, txpr_str(src), t_str(dest))

def constelemptr_str(src, ixs):
    return 'getelementptr (%s, %s)' % (txpr_str(src), ', '.join(
            'i32 %d' % ix for ix in ixs))

def clear_indent():
    env(LOCALS).needIndent = False

def temp_reg():
    lcl = env(LOCALS)
    reg = Tmp(lcl.tempCtr)
    lcl.tempCtr += 1
    return reg

def temp_reg_named(nm):
    lcl = env(LOCALS)
    reg = Reg('%s.%d' % (nm, lcl.tempCtr))
    lcl.tempCtr += 1
    return reg

def null():
    return ConstKeyword(KNull())
def zeroinitializer():
    return ConstKeyword(KZeroInitializer())

# INSTRUCTIONS

def load(regname, t, xpr):
    tmp = temp_reg_named(regname)
    out_xpr(tmp)
    out(' = load ')
    out_t_ptr(t)
    out_xpr(xpr)
    newline()
    return TypedXpr(t, tmp)

def store_local_var(txpr, var):
    out('store ')
    out_txpr(txpr)
    comma()
    out_t_ptr(txpr.type)
    out_xpr(extrinsic(LocalReg, var))
    newline()

def store_xpr(txpr, dest):
    out('store ')
    out_txpr(txpr)
    comma()
    out_t_ptr(txpr.type)
    out_xpr(dest)
    newline()

def sizeof(t):
    nullx = ConstElementPtr(TypedXpr(t, null()), [1])
    return ConstCast('ptrtoint', TypedXpr(t, nullx), IInt())

def malloc(t):
    mem = write_runtime_call('malloc', [sizeof(t)])
    return cast(TypedXpr(IVoidPtr(), fromJust(mem)), t)

def call(ftx, argxs):
    tmp = temp_reg()
    out_xpr(tmp)
    out(' = call ')
    out_t(ftx.type.ret)
    out_xpr(ftx.xpr)
    write_args(ftx.type.params, argxs)
    newline()
    return tmp

def call_void(ftx, argxs):
    out('call ')
    out_t(IVoid())
    out_xpr(ftx.xpr)

    ft = ftx.type
    # TEMP
    if matches(ft, "ITuple([f, _])"):
        ft = ft.types[0]

    write_args(ft.params, argxs)
    if ft.meta.noReturn:
        out(' noreturn')
    newline()

def write_args(paramTypes, args):
    out('(')
    first = True
    for p, x in ezip(paramTypes, args):
        if first:
            first = False
        else:
            comma()
        out_t(match(p, "IParam(t, _)"))
        out_xpr(x)
    out(')')

def get_element_ptr(name, tx, index):
    if is_const(tx.xpr):
        return ConstElementPtr(tx, [0, index])
    tmp = temp_reg_named(name)
    out_xpr(tmp)
    out(' = getelementptr inbounds ')
    out_txpr(tx)
    comma()
    out('i32 0')
    comma()
    out('i32 %d' % (index,))
    newline()
    return tmp

def get_field_ptr(tx, f):
    index = extrinsic(FieldIndex, f)
    return get_element_ptr(extrinsic(expand.FieldSymbol, f), tx, index)

def subscript(regname, arraytx, itx):
    arrayPtr = temp_reg_named('arrayptr')
    out_xpr(arrayPtr)
    out(' = getelementptr ')
    out_txpr(arraytx)
    comma()
    out('i32 0')
    comma()
    out_txpr(itx)
    newline()
    elemType = match(arraytx.type, 'IPtr(IArray(0, t))')
    return load(regname, elemType, arrayPtr).xpr

def extractvalue(regname, tx, index):
    # Const version would be fairly pointless
    tmp = temp_reg_named(regname)
    out_xpr(tmp)
    out(' = extractvalue ')
    out_txpr(tx)
    comma()
    out(str(index))
    newline()
    return tmp

def insertvalue(tx, value, index):
    tmp = temp_reg()
    out_xpr(tmp)
    out(' = insertvalue ')
    out_txpr(tx)
    comma()
    out_txpr(value)
    comma()
    out(str(index))
    newline()
    return tmp

def build_struct(t, args):
    accum = ConstKeyword(KZeroInitializer())
    for i, argtx in enumerate(args):
        if matches(argtx.xpr, 'ConstInt(0) or ConstFloat(0.0) or ' +
                    'ConstKeyword(KNull())'):
            continue
        accum = insertvalue(TypedXpr(t, accum), argtx, i)
    return TypedXpr(t, accum)

def _do_cast(txpr, dest, liberal):
    src = txpr.type
    if matches((src, dest), '(IVoidPtr(), IVoidPtr())'):
        return txpr
    if itypes_equal(src, dest):
        if liberal:
            return txpr
        assert False, "Pointless %s cast to itself" % (src,)
    kind = match((src, dest),
        ('(IInt() or IBool(), IVoidPtr() or IPtr(_))', lambda: 'inttoptr'),
        ('(IVoidPtr() or IPtr(_), IInt() or IBool())', lambda: 'ptrtoint'),
        ('(IVoidPtr() or IPtr(_), IVoidPtr() or IPtr(_))', lambda: 'bitcast'),
        ('(IInt(), IFloat())', lambda: 'sitofp'),
        ('(IFloat(), IInt())', lambda: 'fptosi'),
        ('(IInt(), IInt64())', lambda: 'sext'),
        ('(IInt64(), IInt())', lambda: 'trunc'),
        ('_', lambda: 'invalid'))
    assert kind != 'invalid', "Can't cast %s to %s" % (src, dest)
    xpr = txpr.xpr
    if is_const(xpr):
        return TypedXpr(dest, ConstCast(kind, txpr, dest))
    tmp = temp_reg_named(kind)
    out_xpr(tmp)
    out(' = %s ' % (kind,))
    out_txpr(txpr)
    out(' to ')
    out_t_nospace(dest)
    newline()
    return TypedXpr(dest, tmp)

def cast(txpr, dest):
    return _do_cast(txpr, dest, False)

def cast_if_needed(txpr, dest):
    return _do_cast(txpr, dest, True)

_cached_runtime_refs = {}
def runtime_decl(name):
    # "Proper" impl of this module will just point at the decls directly
    ref = _cached_runtime_refs.get(name)
    if ref is not None:
        return ref
    runtime = loaded_modules['runtime']
    from astconv import loaded_module_export_names, valueNamespace
    symbolTable = loaded_module_export_names[runtime]
    ref = symbolTable[(name, valueNamespace)]
    _cached_runtime_refs[name] = ref
    return ref

# TYPES

def typeof(e):
    assert isinstance(e, (LExpr, Var, GlobalVar, Field)), \
            "%s is not type-y" % (e,)
    return extrinsic(LLVMTypeOf, e)

def t_str(t):
    return match(t,
        ("IInt()", lambda: "i32"),
        ("IInt64()", lambda: "i64"),
        ("IByte()", lambda: "i8"),
        ("IBool()", lambda: "i1"),
        ("IFloat()", lambda: "float"),
        ("IVoid()", lambda: "void"),
        ("IArray(n, t)", lambda n, et: "[%d x %s]" % (n, t_str(et))),
        ("ITuple(ts)", lambda ts: "{%s}" % (', '.join(map(t_str, ts)))),
        ("IData(dt) or IDataCtor(dt)", lambda dt: "%%%s" % extrinsic(Name,dt)),
        ("IFunc(ps, r, _)", _ifunc_str),
        ("IPtr(p)", lambda p: t_str(p) + "*"),
        ("IWeak(t)", t_str),
        ("IVoidPtr()", lambda: "i8*"))

def _ifunc_str(ps, r):
    return "%s (%s)*" % (t_str(r), ', '.join(
            t_str(match(p, "IParam(t, _)")) for p in ps))

def out_t(t):
    out('%s ' % (t_str(t),))
def out_t_ptr(t):
    out('%s* ' % (t_str(t),))
def out_t_nospace(t):
    out(t_str(t))

def out_txpr(tx):
    out_t(tx.type)
    out_xpr(tx.xpr)

# EXPRESSIONS

# Ought to specify a dependency on Bindable somehow
LLVMBindable = new_typeclass('LLVMBindable',
        ('express', 'a -> Xpr'),
        ('express_called', '(a, [LExpr]) -> Maybe(Xpr)',
                         lambda target, args: Nothing()))

@impl(LLVMBindable, Builtin)
def express_Builtin(b):
    return match(b, ('key("True")', lambda: ConstKeyword(KTrue())),
                    ('key("False")', lambda: ConstKeyword(KFalse())),
                    ('key("free_buffer")', lambda:
                                global_symbol(runtime_decl('free'))))

@impl(LLVMBindable, GlobalVar)
def express_GlobalVar(v):
    repl = extrinsic(expand.GlobalSymbol, v)
    if repl.isFunc:
        return Global(repl.symbol)
    elif has_extrinsic(LiteralSize, v):
        return get_strlit_ptr(v)
    else:
        return load(repl.symbol, typeof(v), Global(repl.symbol)).xpr

@impl(LLVMBindable, Var)
def express_Var(v):
    return load_var(v)

@impl(LLVMBindable, Register)
def express_Register(r):
    return Reg(extrinsic(expand.LocalSymbol, r))

def load_var(v):
    reg = extrinsic(LocalReg, v)
    return load(reg.label, typeof(v), reg).xpr

@impl(LLVMBindable, Extrinsic)
def express_Extrinsic(extr):
    return global_symbol(extr)

@impl(LLVMBindable, Env)
def express_Env(e):
    return global_symbol(e)

def una_op(b):
    # grr boilerplate
    return match(b,
        ('key("not")', lambda: 'not'),
        ('key("negate")', lambda: 'negate'),
        ('key("fnegate")', lambda: 'fnegate'),
        ('key("float")', lambda: 'int_to_float'),
        ('key("int")', lambda: 'float_to_int'),
        ('key("len")', lambda: 'len'), ('key("buffer")', lambda: 'buffer'),
        ('_', lambda: '<unknown builtin %s>' % (b,)))

def bin_op(b):
    # grr boilerplate
    return match(b,
        ('key("+")', lambda: 'add'), ('key("-")', lambda: 'sub'),
        ('key("*")', lambda: 'mul'), ('key("//")', lambda: 'sdiv'),
        ('key("%")', lambda: 'srem'),
        ('key("fadd")', lambda: 'fadd'), ('key("fsub")', lambda: 'fsub'),
        ('key("fmul")', lambda: 'fmul'), ('key("fdiv")', lambda: 'fdiv'),
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

def expr_unary(op, arg):
    if op == 'len':
        intT = IIntPtr()
        arg = cast_if_needed(arg, IPtr(IArray(0, intT)))
        l = subscript('len', arg, TypedXpr(intT, ConstInt(-1)))
        if IS64:
            l = cast(TypedXpr(IInt64(), l), IInt()).xpr
        return l
    elif op == 'buffer':
        buf = write_runtime_call('malloc', [arg.xpr])
        return fromJust(buf)
    elif op == 'int_to_float':
        return cast(arg, IFloat()).xpr
    elif op == 'float_to_int':
        return cast(arg, IInt()).xpr

    floating = op.startswith('f')
    if floating:
        instr = 'fsub'
        pivot = TypedXpr(IFloat(), ConstFloat(0.0))
    else:
        instr = 'sub'
        pivot = TypedXpr(arg.type, ConstInt(1 if op == 'not' else 0))
    if is_const(arg.xpr):
        return ConstOp(instr, [pivot, arg])
    else:
        tmp = temp_reg_named(op)
        out_xpr(tmp)
        out(' = %s ' % (instr,))
        out_txpr(pivot)
        comma()
        out_xpr(arg.xpr)
        newline()
        return tmp

def expr_binop(op, left, right, t):
    tleft = TypedXpr(t, left)
    if is_const(left) and is_const(right):
        return ConstOp(op, [tleft, TypedXpr(t, right)])
    else:
        tmp = temp_reg_named(op.split(' ')[-1])
        out_xpr(tmp)
        out(' = %s ' % (op,))
        out_txpr(tleft)
        comma()
        out_xpr(right)
        newline()
        return tmp

def write_runtime_call(name, argxs):
    decl = runtime_decl(name)
    fx = global_symbol(decl)
    declt = extrinsic(LLVMTypeOf, decl)
    ftx = TypedXpr(declt, fx)

    if matches(ftx.type, "IFunc(_, IVoid(), _)"):
        call_void(ftx, argxs)
        return Nothing()
    else:
        return Just(call(ftx, argxs))

def expr_call(var, args):
    mret = LLVMBindable.express_called(var, args)
    if isJust(mret):
        return fromJust(mret)

    ftx = TypedXpr(extrinsic(LLVMTypeOf, var), LLVMBindable.express(var))
    argxs = map(express, args)

    rett = match(ftx.type, "IFunc(_, t, _)")
    assert not matches(rett, "IVoid()")

    return call(ftx, argxs)

def expr_call_indirect(f, args, envParam):
    fvaltx = express_typed(f)
    argxs = map(express, args)

    ft = match(fvaltx.type, "ITuple([f==IFunc(_, _, _), _])")
    assert not matches(ft.ret, "IVoid()")

    fx = extractvalue('fptr', fvaltx, 0)
    if envParam:
        argxs.append(extractvalue('fctx', fvaltx, 1))

    return call(TypedXpr(ft, fx), argxs)

@impl(LLVMBindable, Builtin)
def express_called_Builtin(target, args):
    op = una_op(target)
    if not op.startswith('<unknown'):
        assert len(args) == 1, '%s is unary' % (op,)
        arg = args[0]
        if op == 'negate' and matches(arg, 'Lit(IntLit(_))'):
            return Just(ConstInt(-arg.literal.val))
        elif op == 'fnegate' and matches(arg, 'Lit(FloatLit(_))'):
            return Just(ConstFloat(-arg.literal.val))
        return Just(expr_unary(op, express_typed(arg)))

    assert len(args) == 2, '%s requires two args' % (op,)
    t = typeof(args[0])
    left = express(args[0])
    right = express(args[1])

    if matches(target, 'key("subscript")'):
        it = typeof(args[1])
        assert itypes_equal(it, IInt()), "Non-integral index"
        return Just(subscript('subscript',
                TypedXpr(t, left), TypedXpr(it, right)))

    op = bin_op(target)
    return Just(expr_binop(op, left, right, t))

def expr_func(f, ps, body):
    clos = extrinsic(expand.Closure, f)
    assert not clos.isClosure, "TODO"
    return global_symbol(clos.func)

def push_env(envx, ctxVar, init):
    ctx = load_var(ctxVar)
    i = express(init)
    ctx = fromJust(write_runtime_call('_pushenv', [envx, ctx, i]))
    store_var(ctxVar, ctx)

def pop_env(envx, ctxVar):
    ctx = load_var(ctxVar)
    ctx = fromJust(write_runtime_call('_popenv', [envx, ctx]))
    store_var(ctxVar, ctx)

def expr_attr(e, f):
    tx = express_typed(e)
    fieldptr = get_field_ptr(tx, f)
    return load(extrinsic(expand.FieldSymbol, f), typeof(f), fieldptr).xpr

def expr_attr_ix(e):
    tx = express_typed(e)
    ctor = match(typeof(e), "IPtr(IDataCtor(ctor))")
    index = extrinsic(DataLayout, ctor).discrimSlot
    ixptr = get_element_ptr('ix', tx, index)
    return load('_ix', IInt(), ixptr).xpr

def expr_lit(lit):
    return match(lit, ('IntLit(i)', ConstInt),
                      ('FloatLit(f)', ConstFloat))

def get_strlit_ptr(var):
    tmp = temp_reg()
    out_xpr(tmp)
    out(' = getelementptr [%d x i8]* ' % (extrinsic(LiteralSize, var),))
    out_global_symbol(var)
    out(', i32 0, i32 0')
    newline()
    return tmp

def expr_tuplelit(lit, es):
    tupt, tts = match(typeof(lit), ("IPtr(tupt==ITuple(tts))", tuple2))
    tmp = malloc(IPtr(tupt)).xpr
    txs = [TypedXpr(t, express(e)) for t, e in ezip(tts, es)]
    struct = build_struct(tupt, txs)
    store_xpr(struct, tmp)
    return tmp

def expr_listlit(lit, es):
    litt = typeof(lit)
    t = match(litt, "IPtr(IArray(0, t))")
    n = len(es)
    at = IArray(n + 1, t)
    xtmem = malloc(IPtr(at))
    # Store length in first element
    lenx = TypedXpr(IInt(), ConstInt(n))
    if not itypes_equal(IInt(), t):
        lenx = cast(lenx, t)
    txs = [lenx]
    for e in es:
        txs.append(TypedXpr(t, express(e)))
    array = build_struct(at, txs)
    store_xpr(array, xtmem.xpr)
    # Return pointer to second element
    arr = get_element_ptr('listlit', xtmem, 1)
    return cast(TypedXpr(IPtr(t), arr), litt).xpr

def expr_cast(src, dest, e):
    x = express(e)
    return cast(TypedXpr(src, x), dest).xpr

def expr_funcval(e, f, ctx):
    fx = LLVMBindable.express(f)
    assert is_const(fx)
    valt = typeof(e)
    ft = match(valt, "ITuple([f, IVoidPtr()])")
    valx = ConstStruct([TypedXpr(ft, fx),
            TypedXpr(IVoidPtr(), null())])
    if isJust(ctx):
        ctxtx = TypedXpr(IVoidPtr(), load_var(fromJust(ctx)))
        valx = insertvalue(TypedXpr(valt, valx), ctxtx, 1)
    return valx

def expr_with(var, expr):
    store_pat_var(var, TypedXpr(IVoidPtr(), zeroinitializer()))
    return express(expr)

def express(expr):
    return match(expr,
        ('Bind(v)', LLVMBindable.express),
        ('Call(Bind(var), args)', expr_call),
        ('FuncExpr(f==Func(ps, body))', expr_func),
        ('Attr(e, f)', expr_attr),
        ('AttrIx(e)', expr_attr_ix),
        ('Lit(lit)', expr_lit),
        ('lit==TupleLit(es)', expr_tuplelit),
        ('lit==ListLit(es)', expr_listlit),
        ('CallIndirect(f, args, envParam)', expr_call_indirect),
        ('Cast(src, dest, expr)', expr_cast),
        ('e==FuncVal(f, ctx)', expr_funcval),
        ('ReadGlobal(var)', global_symbol),
        ('NullPtr()', null),
        ('SizeOf(t)', sizeof),
        ('Undefined()', lambda: ConstKeyword(KUndef())))

def express_typed(expr):
    return TypedXpr(typeof(expr), express(expr))

# STATEMENTS

def store_var(v, xpr):
    store_local_var(TypedXpr(typeof(v), xpr), v)

def store_attr(dest, f, val):
    tx = express_typed(dest)
    fieldptr = get_field_ptr(tx, f)
    store_xpr(TypedXpr(typeof(f), val), fieldptr)

def store_slot(lhs, dest, ix, val):
    tx = express_typed(dest)
    slotptr = get_element_ptr('slot', tx, ix)
    store_xpr(TypedXpr(extrinsic(LLVMTypeOf, lhs), val), slotptr)

def store_lhs(lhs, x):
    match(lhs,
        ('LhsVar(v)', lambda v: store_var(v, x)),
        ('LhsAttr(e, f)', lambda e, f: store_attr(e, f, x)),
        ('LhsSlot(e, ix)', lambda e, ix: store_slot(lhs, e, ix, x)))

def store_pat_var(v, txpr):
    # might already be set up by GC business
    if not has_extrinsic(LocalReg, v):
        t = txpr.type
        reg = Reg(extrinsic(expand.LocalSymbol, v))
        add_extrinsic(LocalReg, v, reg)
        out_xpr(reg)
        out(' = alloca ')
        out_t_nospace(t)
        newline()

    store_local_var(txpr, v)

def store_pat_tuple(ps, txpr):
    with_pat_tuple(ps, txpr, store_pat)

def with_pat_tuple(ps, txpr, func):
    tupt = match(txpr.type, 'IPtr(t==ITuple(_))')

    tupval = load('tuple', tupt, txpr.xpr)
    for i, p in enumerate(ps):
        func(p, extractvalue('t%d' % (i,), tupval, i))

def store_pat(pat, xpr):
    if has_extrinsic(LLVMPatCast, pat):
        src, dest = extrinsic(LLVMPatCast, pat)
        txpr = cast(TypedXpr(src, xpr), dest)
    else:
        txpr = TypedXpr(extrinsic(LLVMTypeOf, pat), xpr)

    match((pat, txpr), ('(PatVar(v), txpr)', store_pat_var),
                       ('(PatTuple(ps), txpr)', store_pat_tuple),
                       ('(PatWild(), _)', nop))

def load_lhs(lhs):
    return match(lhs,
        ('LhsVar(v)', LLVMBindable.express),
        ('LhsAttr(e, a)', expr_attr))

def write_assign(lhs, e):
    ex = express(e)
    store_lhs(lhs, ex)

def write_augassign(op, lhs, e):
    right = express(e)
    left = load_lhs(lhs)
    ex = expr_binop(aug_op(op), left, right, typeof(e))
    store_lhs(lhs, ex)

def write_local_func_defn(f):
    assert has_extrinsic(expand.Closure, f)

def write_defn(pat, e):
    store_pat(pat, express(e))

def write_field_specs(fields, layout):
    verbose = not env(DECLSONLY)
    if verbose:
        out('{')
        newline()
    else:
        out('{ ')

    specs = []
    if layout.gcSlot >= 0:
        assert layout.gcSlot == len(specs)
        specs.append((IVoidPtr(), "gc"))
    if layout.extrSlot >= 0:
        assert layout.extrSlot == len(specs)
        assert layout.extrSlot == 1 # TEMP
        specs.append((IVoidPtr(), "extrinsics"))
    if layout.discrimSlot >= 0:
        assert layout.discrimSlot == len(specs)
        specs.append((IInt(), "discrim"))
    for f in fields:
        assert extrinsic(FieldIndex, f) == len(specs)
        specs.append((typeof(f), extrinsic(expand.FieldSymbol, f)))

    n = len(specs)
    for i, (t, nm) in enumerate(specs):
        if verbose:
            out('  ')
        out_t_nospace(t)
        if i < n - 1:
            comma()
        elif verbose:
            out('  ')
        if verbose:
            out('; %s' % (nm,))
            newline()
    if verbose:
        out('}')
    else:
        out(' }')

def write_dtstmt(form):
    layout = extrinsic(DataLayout, form)
    if layout.discrimSlot >= 0:
        out('%%%s = type opaque' % (global_symbol_str(form),))
        newline()
    for ctor in form.ctors:
        if Nullable.isMaybe(ctor):
            continue # XXX maybe codegen
        out('%%%s = type ' % (global_symbol_str(ctor),))
        write_field_specs(ctor.fields, layout)
        newline()
    if not env(DECLSONLY):
        newline()

def write_void_call(f, a):
    fx = express_typed(f)
    argxs = map(express, a)
    call_void(fx, argxs)

def write_new_env(e):
    decl = env(DECLSONLY)
    out_global_symbol(e)
    out(' = %s global %%Env' % ('external' if decl else 'linkonce',))
    if not decl:
        out(' zeroinitializer')
    newline()

def write_new_extrinsic(extr):
    decl = env(DECLSONLY)
    out_global_symbol(extr)
    out(' = %s global %%Extrinsic' % ('external' if decl else 'linkonce',))
    if not decl:
        out(' zeroinitializer')
    newline()

def write_param_types(tps):
    out('(')
    first = True
    for t in tps:
        if first:
            first = False
        else:
            comma()
        out_t_nospace(match(t, "IParam(t, _)"))
    out(')')

def write_params(ps, tps):
    out('(')
    first = True
    txs = []
    for p, tp in ezip(ps, tps):
        if first:
            first = False
        else:
            comma()
        tmp = match(p,
            ('LVar(v)',
                lambda v: temp_reg_named(extrinsic(expand.LocalSymbol, v))),
            ('LRegister(r)',
                lambda r: Reg(extrinsic(expand.LocalSymbol, r), 0)))
        tx = TypedXpr(match(tp, 'IParam(t, _)'), tmp)
        out_txpr(tx)
        txs.append(tx)
    out(')')
    return txs

def write_func_decl(ref, ft):
    out('declare ')
    out_t(ft.ret)
    out_xpr(ref)
    write_param_types(ft.params)
    if ft.meta.noReturn:
        out(' noreturn')
    newline()

def write_func(f):
    ft = extrinsic(LLVMTypeOf, f.var)

    if env(DECLSONLY):
        write_func_decl(global_symbol(f.var), ft)
        return
    elif env(EXPORTSYMS):
        out('define ')
    else:
        out('define internal ')
    out_t(ft.ret)
    out_global_symbol(f.var)

    as_local(lambda: _write_func(f, ft))
    out('}\n\n')

def _write_func(f, ft):
    txs = write_params(f.params, ft.params)
    if ft.meta.noReturn:
        out(' noreturn')
    if IS64:
        out(' uwtable')
    out(' nounwind ssp gc "shadow-stack" {')
    newline()

    if len(f.gcVars) > 0 or len(f.params) > 0:
        for entry in f.gcVars:
            var = entry.var
            reg = Reg(extrinsic(expand.LocalSymbol, var))
            add_extrinsic(LocalReg, var, reg)
            out_xpr(reg)
            out(' = alloca ')
            t = extrinsic(LLVMTypeOf, var)
            out_t(t)
            newline()

            pt = cast_if_needed(TypedXpr(IPtr(t), reg), IPtr(IVoidPtr()))
            out('call void @llvm.gcroot(')
            out_txpr(pt)
            comma()
            m = match(entry.formVar)
            if m('Just(formVar)'):
                out('i8* ')
                out_global_symbol(m.formVar)
                out(')')
            else:
                out('i8* null)')
            newline()

        # write params to mem
        for p, tx in ezip(f.params, txs):
            m = match(p)
            if m('LVar(v)'):
                # this is kind of a goofy check
                if not has_extrinsic(LocalReg, m.v):
                    reg = Reg(extrinsic(expand.LocalSymbol, m.v))
                    add_extrinsic(LocalReg, m.v, reg)
                    out_xpr(reg)
                    out(' = alloca ')
                    out_t(tx.type)
                    newline()
                store_local_var(tx, m.v)

        newline()

    for block in f.blocks:
        write_block(block)

def write_stmt(stmt):
    if has_extrinsic(IRComments, stmt):
        map_(out_comment, extrinsic(IRComments, stmt))
    out_pretty(stmt, 'Stmt(LExpr)')
    match(stmt,
        ("Assign(lhs, e)", write_assign),
        ("AugAssign(op, lhs, e)", write_augassign),
        ("Defn(PatVar(_), FuncExpr(f))", write_local_func_defn),
        ("Defn(pat, e)", write_defn),
        ("VoidStmt(VoidCall(f, a))", write_void_call),
        ("Nop()", nop))

def write_block(block):
    if block.label != '.0':
        imm_out('\n%s:\n' % (block.label,))
    env(LOCALS).needIndent = True
    map_(write_stmt, block.stmts)

    nullCount = len(block.nullOuts)
    if nullCount > 0:
        out_comment('lifetimes end' if nullCount > 1 else 'lifetime ends')
        for var in block.nullOuts:
            store_local_var(TypedXpr(typeof(var), null()), var)

    m = match(block.terminator)
    if m('TermJump(Just(dest))'):
        out('br ')
        out_block_ref(m.dest)
    elif m('TermJumpCond(c, Just(t), Just(f))'):
        out_comment('if %s' % (stringify(m.c, 'LExpr'),))
        cx = express(m.c)
        out('br i1 ')
        out_xpr(cx)
        comma()
        out_block_ref(m.t)
        comma()
        out_block_ref(m.f)
    elif m('TermReturn(e)'):
        out_comment('return %s' % (stringify(m.e, 'LExpr'),))
        tx = express_typed(m.e)
        out('ret ')
        out_txpr(tx)
    elif m('TermReturnNothing()'):
        out('ret void')
    elif m('TermUnreachable()'):
        out('unreachable')
    else:
        assert False
    newline()


# TYPE REPRESENTATIONS

def write_ctor_form_fields(ctor, gcFields):
    assert len(gcFields) < 256
    first = True
    for field in gcFields:
        if first:
            first = False
        else:
            comma()
        newline()
        # field offset
        nullPtr = TypedXpr(IPtr(IDataCtor(ctor)), null())
        fieldIndex = extrinsic(FieldIndex, field)
        fieldPtr = ConstElementPtr(nullPtr, [0, fieldIndex])
        fieldTx = TypedXpr(IPtr(extrinsic(LLVMTypeOf, field)), fieldPtr)
        out('<{i8, i8*}> <{i8 ')
        out_xpr(ConstCast('ptrtoint', fieldTx, IByte()))
        comma()

        # pointer to form
        out('i8* ')
        m = match(type_layout_form_var(field.type))
        if m('Just(v)'):
            out_global_symbol(m.v)
        else:
            out('null')
        out('}>')
    newline()

def write_dtform(form):
    assert not env(DECLSONLY)
    layout = extrinsic(DataLayout, form)
    if layout.gcSlot < 0:
        return

    written = False
    form_tbl = []
    for ctor in form.ctors:
        # field type list for precise GC
        clayout = extrinsic(CtorLayout, ctor)
        if isNothing(clayout.formVar):
            form_tbl.append(null())
            continue

        ctorName, nameLen = escape_strlit(extrinsic(Name, ctor))

        sym = global_symbol(fromJust(clayout.formVar))
        sym_ = sym_with_underscore(sym)
        vecT = '[%d x <{i8, i8*}>]' % (len(clayout.fields),)
        nameT = '[%d x i8]' % (nameLen,)
        fullT = '<{i8, %s, %s}>' % (vecT, nameT)
        out_xpr(sym_)
        out(' = internal constant %s <{' % (fullT,))
        newline()
        out('i8 %d, %s [' % (len(clayout.fields), vecT))
        write_ctor_form_fields(ctor, clayout.fields)
        out('], %s %s}>, align %d' % (nameT, ctorName, mach.PTRSIZE))
        newline()

        out_xpr(sym)
        out(' = alias internal i8* bitcast (%s* ' % (fullT,))
        out_xpr(sym_)
        out(' to i8*)')
        newline()

        form_tbl.append(sym)
        written = True

    if layout.discrimSlot >= 0:
        # discrim->ctor form lookup table
        dtsym = global_symbol(fromJust(layout.tblVar))
        dtsym_ = sym_with_underscore(dtsym)
        fullT = '[%d x i8*]' % (len(form_tbl),)

        out_xpr(dtsym_)
        out(' = internal constant %s [' % (fullT,))
        first = True
        for sym in form_tbl:
            if first:
                first = False
            else:
                comma()
            out('i8* ')
            out_xpr(sym)
        out('], align %d' % (mach.PTRSIZE,))
        newline()

        out_xpr(dtsym)
        out(' = alias internal i8* bitcast (%s* ' % (fullT,))
        out_xpr(dtsym_)
        out(' to i8*)')
        written = True

    if written:
        newline()

def sym_with_underscore(sym):
    # hack: this ought to be uniqued properly in expand
    return Global(sym.name + '_')

# TOP-LEVEL

def imported_bindable_used(v):
    return v in env(expand.IMPORTBINDS)

def write_top_cdecl(v):
    if not imported_bindable_used(v):
        return
    write_func_decl(global_symbol(v), extrinsic(LLVMTypeOf, v))

def write_top_var_func(v, f):
    if env(DECLSONLY) and not imported_bindable_used(v):
        return
    write_top_func(v, f)

def escape_strlit(s):
    b = s.encode('utf-8')
    n = len(b) + 1
    lit = 'c"'
    for c in iter(b):
        i = ord(c)
        lit += c if 31 < i < 127 else '\\%02x' % (i,)
    return (lit + '\\00"', n)

def write_top_lit(v, lit):
    if env(DECLSONLY) and not imported_bindable_used(v):
        return
    m = match(lit)
    if m("StrLit(s)"):
        escaped, n = escape_strlit(m.s)
        add_extrinsic(LiteralSize, v, n)
        out_global_symbol(v)
        out(' = private unnamed_addr constant [%d x i8] ' % (n,))
        out(escaped)
    else:
        out_global_symbol(v)
        out(' = internal constant ')
        out_t(typeof(v))
        out_xpr(expr_lit(lit))
    newline()

def write_top_decls(decls):
    map_(write_top_cdecl, decls.cdecls)
    map_(write_dtstmt, decls.dts)
    map_(write_new_env, decls.envs)
    map_(write_new_extrinsic, decls.extrinsics)
    for lit in decls.lits:
        write_top_lit(lit.var, lit.literal)
    map_(write_top_cdecl, decls.funcDecls)

def write_top_decls_post_impl(decls):
    # extra impl-only data, end of file
    map_(write_dtform, decls.dts)

def as_local(f):
    in_env(LOCALS, IRLocals(False, 0), f)

def write_unit(unit):
    for func in unit.funcs:
        scope_extrinsic(LocalReg, lambda: write_func(func))

prelude = """; prelude
%Type = type opaque
%Env = type i8
%Extrinsic = type i8
declare void @llvm.gcroot(i8** %ptrloc, i8* %metadata)

"""

def write_imports(dep):
    dt = match(dep.rootType, 'TData(dt, _)')
    if dt is extrinsic(FormSpec, DATATYPES['ModuleDecls']):
        out('; %s' % (extrinsic(Name, dep),))
        newline()
        in_env(DECLSONLY, True, lambda: write_top_decls(dep.root))

LLFile = new_extrinsic('LLFile', str, omni=True)
OFile = new_extrinsic('OFile', str, omni=True)

OwnDecls = new_extrinsic('OwnDecls', ['*Module'], omni=True)

def write_ir(decl_mod, xdecl_mod, defn_mod, filename):

    decls = [decl_mod, xdecl_mod]
    add_extrinsic(OwnDecls, defn_mod, decls)

    def go():
        out(prelude)

        # XXX force runtime import until we have better staged compilation
        runtime = loaded_modules['runtime']
        write_imports(runtime)
        walk_deps(write_imports, defn_mod, set(decls + [runtime]))

        newline()
        out('; main')
        newline()
        def go2():
            for decl in decls:
                write_top_decls(decl.root)
            in_env(EXPORTSYMS, True, lambda: write_unit(defn_mod.root))
            for decl in decls:
                write_top_decls_post_impl(decl.root)
        in_env(DECLSONLY, False, go2)

    in_env(IR, file(filename, 'wb'), # really ought to close explicitly
        lambda: scope_extrinsic(LiteralSize,
        go))

    add_extrinsic(LLFile, decl_mod, filename)

def compile(mod):
    ll = extrinsic(LLFile, mod)
    s = ll + '.s'
    o = ll + '.o'
    if os.system('llc -o %s %s' % (s, ll)) != 0:
        return False
    if os.system('cc -c -o %s %s' % (o, s)) != 0:
        return False
    add_extrinsic(OFile, mod, o)
    return True

def link(decl_mod, defn_mod, binary):
    objs = []

    def add_obj(dep):
        dt = dep.rootType.data
        if dt is extrinsic(FormSpec, DATATYPES['ModuleDecls']):
            if not has_extrinsic(OFile, dep):
                print col('Yellow', 'omitting missing'), extrinsic(Name, dep)
                return
            objs.append(extrinsic(OFile, dep))
    walk_deps(add_obj, defn_mod, set(extrinsic(OwnDecls, defn_mod)))

    objs.append(extrinsic(OFile, decl_mod))
    return os.system('cc -o %s %s' % (binary, ' '.join(objs))) == 0

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
