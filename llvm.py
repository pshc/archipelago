from atom import *
from quilt import *
import expand
import mach
import os
import sys

Label = DT('Label', ('name', str),
                    ('used', bool),
                    ('needsTerminator', bool))

IRInfo = DT('IRInfo', ('stream', None),
                      ('overrideImportUsageCheck', bool))
IR = new_env('IR', IRInfo)

IRLocals = DT('IRLocals', ('needIndent', bool),
                          ('unreachable', bool),
                          ('tempCtr', int),
                          ('entryBlock', Label),
                          ('currentBlock', Label),
                          ('labelsUsed', set([str])),
                          ('loopLabels', 'Maybe((Label, Label))'))

LOCALS = new_env('LOCALS', IRLocals)

EXPORTSYMS = new_env('EXPORTSYMS', bool)

DECLSONLY = new_env('DECLSONLY', bool)

def setup_ir(filename):
    stream = file(filename, 'wb') # really ought to close explicitly
    return IRInfo(stream, False)

def setup_locals():
    entry = Label(':entry:', True, True)
    return IRLocals(False, False, 0, entry, entry, set(), Nothing())

TypedXpr = DT('TypedXpr', ('type', IType), ('xpr', 'Xpr'))

Xpr, Reg, Tmp, Global, ConstStruct, Const, ConstOp, ConstCast, \
    ConstElementPtr = ADT('Xpr',
        'Reg', ('label', 'str'), ('index', 'int'),
        'Tmp', ('index', 'int'),
        'Global', ('name', str),
        'ConstStruct', ('vals', [TypedXpr]),
        'Const', ('frag', 'str'),
        'ConstOp', ('op', 'str'), ('args', [TypedXpr]),
        'ConstCast', ('kind', str), ('src', TypedXpr), ('dest', IType),
        'ConstElementPtr', ('src', TypedXpr), ('indexes', [int]))

def is_const(x):
    return match(x,
        ('Reg(_, _)', lambda: False), ('Tmp(_)', lambda: False),
        ('Global(_)', lambda: True), ('ConstStruct(_)', lambda: True),
        ('Const(_)', lambda: True), ('ConstOp(_, _)', lambda: True),
        ('ConstCast(_, _, _)', lambda: True),
        ('ConstElementPtr(_, _)', lambda: True))

LiteralSize = new_extrinsic('LiteralSize', int)

# GLOBAL OUTPUT

def imm_out(s):
    env(IR).stream.write(s)
    if not env(GENOPTS).quiet:
        sys.stdout.write(s)

def out(s):
    if have_env(LOCALS) and env(LOCALS).needIndent:
        imm_out('  %s' % (s,))
        clear_indent()
    else:
        imm_out(s)

def global_symbol(var):
    return Global(extrinsic(expand.GlobalSymbol, var).symbol)

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

def out_name_reg(a):
    out('%%%s' % (extrinsic(Name, a),))

def out_label(label):
    lcl = env(LOCALS)
    if lcl.currentBlock.needsTerminator:
        out('br label %%%s\n\n%s:\n' % (label.name, label.name))
    else:
        imm_out('\n%s:\n' % (label.name,))
    lcl.currentBlock = label
    lcl.needIndent = True
    lcl.unreachable = False

def out_naked_label_ref(label, naked):
    out(('%%%s' if naked else 'label %%%s') % (label.name,))
    label.used = True

def out_label_ref(label):
    out_naked_label_ref(label, False)

def out_xpr(x):
    out(xpr_str(x))

def xpr_str(x):
    return match(x, ('Reg(nm, i)', lambda nm, i: '%%%s.%d' % (nm, i)),
                    ('Tmp(i)', lambda i: '%%.%d' % (i,)),
                    ('Global(name)', lambda name: '@%s' % (name,)),
                    ('ConstStruct(vals)', conststruct_str),
                    ('Const(s)', identity),
                    ('ConstOp(f, args)', constop_str),
                    ('ConstCast(kind, src, dest)', constcast_str),
                    ('ConstElementPtr(src, ixs)', constelemptr_str))

def txpr_str(txpr):
    return '%s %s' % (t_str(txpr.type), xpr_str(txpr.xpr))

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

def term():
    env(LOCALS).currentBlock.needsTerminator = False
    newline()
    env(LOCALS).unreachable = True

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

def new_series(atom):
    return extrinsic(Location, atom).index

def new_label(nm, series):
    lcl = env(LOCALS)
    nm = '%s.%d' % (nm, series)
    assert nm not in lcl.labelsUsed, "Repeated label %s" % (nm,)
    lcl.labelsUsed.add(nm)
    label = Label(nm, False, True)
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

def phi(reg, t, srcs):
    assert len(srcs) > 1
    out_xpr(reg)
    out(' = phi ')
    out_t(t)
    for i, (xpr, lbl) in enumerate(srcs):
        if i > 0:
            comma()
        out('[ ')
        out_xpr(xpr)
        comma()
        out_naked_label_ref(lbl, True)
        out(' ]')
    newline()

def load(regname, t, xpr):
    tmp = temp_reg_named(regname)
    out_xpr(tmp)
    out(' = load ')
    out_t_ptr(t)
    out_xpr(xpr)
    newline()
    return TypedXpr(t, tmp)

def store_named(txpr, named):
    out('store ')
    out_txpr(txpr)
    comma()
    out_t_ptr(txpr.type)
    out_name_reg(named)
    newline()

def store_xpr(txpr, dest):
    out('store ')
    out_txpr(txpr)
    comma()
    out_t_ptr(txpr.type)
    out_xpr(dest)
    newline()

def malloc(t):
    nullx = ConstElementPtr(TypedXpr(IPtr(t), Const("null")), [1])
    sizeoft = IInt()
    sizeof = ConstCast('ptrtoint', TypedXpr(IPtr(t), nullx), sizeoft)
    mem = write_runtime_call('malloc', [TypedXpr(sizeoft, sizeof)], IVoidPtr())
    return cast(fromJust(mem), IPtr(t))

def call(rett, fx, argxs):
    tmp = temp_reg()
    out_xpr(tmp)
    out(' = call ')
    out_t(rett)
    out_xpr(fx)
    write_args(argxs)
    newline()
    return TypedXpr(rett, tmp)

def call_void(fx, argxs):
    out('call ')
    out_t(IVoid())
    out_xpr(fx)
    write_args(argxs)
    newline()

def write_args(args):
    out('(')
    first = True
    for tx in args:
        if first:
            first = False
        else:
            comma()
        out_txpr(tx)
    out(')')

def get_element_ptr(name, tx, index):
    if is_const(tx.xpr):
        return ConstElementPtr(tx, [0, index])
    tmp = temp_reg_named(name)
    out_xpr(tmp)
    out(' = getelementptr ')
    out_txpr(tx)
    comma()
    out('i32 0')
    comma()
    out('i32 %d' % (index,))
    newline()
    return tmp

def get_field_ptr(tx, f):
    index = extrinsic(expand.FieldIndex, f)
    return get_element_ptr(extrinsic(Name, f), tx, index)

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

def build_struct(t, args):
    i = 0
    accum = Const('undef')
    for argx in args:
        new_val = temp_reg()
        out_xpr(new_val)
        out(' = insertvalue ')
        out_t(t)
        out_xpr(accum)
        comma()
        out_txpr(argx)
        comma()
        out(str(i))
        newline()
        i += 1
        accum = new_val
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
        ('(IInt() or IBool(), IVoidPtr())', lambda: 'inttoptr'),
        ('(IVoidPtr(), IInt() or IBool())', lambda: 'ptrtoint'),
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
    assert isinstance(e, (Expr, Var, Field)), "%s is not type-y" % (e,)
    return extrinsic(LLVMTypeOf, e)

def t_str(t):
    return match(t,
        ("IInt()", lambda: "i32"),
        ("IInt64()", lambda: "i64"),
        ("IFloat()", lambda: "float"),
        ("IBool()", lambda: "i1"),
        ("IVoid()", lambda: "void"),
        ("IArray(n, t)", lambda n, et: "[%d x %s]" % (n, t_str(et))),
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

def out_txpr(tx):
    out_t(tx.type)
    out_xpr(tx.xpr)

# EXPRESSIONS

def expr_and(e, l, r):
    srs = new_series(e)
    entry = new_label('and', srs)
    out_label(entry)
    left = express(l)
    both = new_label('both', srs)
    end = new_label('endand', srs)
    br_cond(left, both, end)
    # left was true
    out_label(both)
    right = express(r)
    br(end)
    # short-circuit with phi
    out_label(end)
    truth = temp_reg_named('and')
    phi(truth, IBool(), [(right, both), (Const('false'), entry)])
    return truth

def expr_or(e, l, r):
    srs = new_series(e)
    entry = new_label('or', srs)
    out_label(entry)
    left = express(l)
    both = new_label('both', srs)
    end = new_label('endor', srs)
    br_cond(left, end, both)
    # left was false
    out_label(both)
    right = express(r)
    br(end)
    # short-circuit with phi
    out_label(end)
    truth = temp_reg_named('or')
    phi(truth, IBool(), [(right, both), (Const('true'), entry)])
    return truth

def expr_ternary(e, c, t, f):
    cond = express(c)
    srs = new_series(e)
    yes = new_label('yes', srs)
    no = new_label('no', srs)
    end = new_label('endternary', srs)
    br_cond(cond, yes, no)

    out_label(yes)
    true = express(t)
    br(end)

    out_label(no)
    false = express(f)
    br(end)

    out_label(end)
    result = temp_reg_named('either')
    phi(result, typeof(t), [(true, yes), (false, no)])
    return result

# Ought to specify a dependency on Bindable somehow
LLVMBindable = new_typeclass('LLVMBindable',
        ('express', 'a -> Xpr'),
        ('express_called', '(a, [Expr]) -> Maybe(Xpr)',
                         lambda target, args: Nothing()),
        ('express_called_void', '(a, [Expr]) -> bool',
                         lambda target, args: False))

@impl(LLVMBindable, Builtin)
def express_Builtin(b):
    return match(b,
        ('key("True")', lambda: Const('true')),
        ('key("False")', lambda: Const('false')))

@impl(LLVMBindable, Var)
def express_Var(v):
    if has_extrinsic(expand.GlobalSymbol, v):
        repl = extrinsic(expand.GlobalSymbol, v)
        if repl.isFunc:
            return Global(repl.symbol)
        elif has_extrinsic(LiteralSize, v):
            return get_strlit_ptr(v)
        else:
            return load(extrinsic(Name, v), typeof(v), Global(repl.symbol)).xpr
    elif has_extrinsic(expand.StaticSymbol, v):
        return Global(extrinsic(expand.StaticSymbol, v))
    else:
        return load_var(v)

def load_var(v):
    # Would be nice: (need name_reg)
    #return load(extrinsic(Name, v), typeof(v), name_reg(v)).xpr
    tmp = temp_reg_named(extrinsic(Name, v))
    out_xpr(tmp)
    out(' = load ')
    out_t_ptr(typeof(v))
    out_name_reg(v)
    newline()
    return tmp

@impl(LLVMBindable, Ctor)
def express_Ctor(c):
    return global_symbol(c)

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

IS64 = (mach.PTRSIZE == 8)

def intptr_type():
    return IInt64() if IS64 else IInt()

def expr_unary(op, arg):
    if op == 'len':
        intT = intptr_type()
        arg = cast_if_needed(arg, IPtr(IArray(0, intT)))
        l = subscript('len', arg, TypedXpr(intT, Const('-1')))
        if IS64:
            l = cast(TypedXpr(IInt64(), l), IInt()).xpr
        return l
    elif op == 'buffer':
        buf = write_runtime_call('malloc', [arg], IVoidPtr())
        return fromJust(buf).xpr
    elif op == 'int_to_float':
        return cast(arg, IFloat()).xpr
    elif op == 'float_to_int':
        return cast(arg, IInt()).xpr

    floating = op.startswith('f')
    pivotVal = '1' if op == 'not' else ('0.0' if floating else '0')
    pivot = TypedXpr(arg.type, Const(pivotVal))
    instr = 'fsub' if floating else 'sub'
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

def write_call(f, args, rett):
    fx = express_casted(f)
    argxs = [express_casted(arg) for arg in args]

    if matches(rett, "IVoid()"):
        call_void(fx.xpr, argxs)
        return Nothing()

    return Just(call(rett, fx.xpr, argxs))

def write_runtime_call(name, argxs, rett):
    fx = global_symbol(runtime_decl(name))

    if matches(rett, "IVoid()"):
        call_void(fx, argxs)
        return Nothing()
    else:
        return Just(call(rett, fx, argxs))

def expr_call(e, f, args):
    if matches(f, 'Bind(_)'):
        mret = LLVMBindable.express_called(f.target, args)
        if isJust(mret):
            return fromJust(mret)
    return fromJust(write_call(f, args, typeof(e))).xpr

@impl(LLVMBindable, Builtin)
def express_called_Builtin(target, args):
    op = una_op(target)
    if not op.startswith('<unknown'):
        assert len(args) == 1, '%s is unary' % (op,)
        arg = args[0]
        if op == 'negate' and matches(arg, 'Lit(IntLit(_))'):
            return Just(Const('%d' % (-arg.literal.val,)))
        elif op == 'fnegate' and matches(arg, 'Lit(FloatLit(_))'):
            return Just(Const('%f' % (-arg.literal.val,)))
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

def push_env(envtx, ctxVar, init):
    # XXX temp hack for this env impl
    # name_reg() would make it cleaner but yagni
    # taking this ptr-to-alloca breaks mem2reg
    # prefer to return a tuple from _pushenv or have it manage its own stack
    pctx = TypedXpr(IPtr(IVoidPtr()),
            Const('%%%s' % (extrinsic(Name, ctxVar),)))

    i = express_typed(init)
    old = write_runtime_call('_pushenv', [envtx, pctx, i], envtx.type)
    return fromJust(old)

def pop_env(envtx, ctxVar, old):
    ctx = TypedXpr(typeof(ctxVar), load_var(ctxVar))
    write_runtime_call('_popenv', [envtx, ctx, old], IVoid())

def expr_inenv(e, environ, init, expr):
    envtx = TypedXpr(extrinsic(LLVMTypeOf, environ), global_symbol(environ))
    ctxVar = extrinsic(expand.InEnvCtxVar, e)
    old = push_env(envtx, ctxVar, init)
    ret = express(expr)
    pop_env(envtx, ctxVar, old)
    return ret

def expr_inenv_void(e, environ, init, expr):
    envtx = TypedXpr(extrinsic(LLVMTypeOf, environ), global_symbol(environ))
    ctx = extrinsic(expand.InEnvCtxVar, e)
    old = push_env(envtx, ctx, init)
    write_void_stmt(expr)
    pop_env(envtx, ctx, old)

def expr_match(m, e, cs):
    tx = express_typed(e)
    msrs = new_series(m)
    next_case = new_label('case', new_series(cs[0]))
    success = new_label('matchresult', msrs)
    phi_srcs = []
    for i, c in enumerate(cs):
        if i > 0:
            assert next_case.used, "Unreachable match case"
        out_label(next_case)
        cp, ce = match(c, ("MatchCase(cp, ce)", tuple2))
        if i + 1 < len(cs):
            next_case = new_label('case', new_series(cs[i+1]))
        else:
            next_case = new_label('failed', msrs)
        info = MatchState(next_case)
        in_env(MATCH, info, lambda: match_pat(cp, tx))
        x = express(ce)
        here = env(LOCALS).currentBlock
        phi_srcs.append((x, here))
        here.used = True
        if not env(LOCALS).unreachable:
            br(success)

    if next_case.used:
        out_label(next_case)
        out('call void @match_fail() noreturn')
        newline()
        out('unreachable')
        term()

    assert success.used
    out_label(success)
    if len(phi_srcs) < 2:
        x, lbl = phi_srcs[0]
        return x
    tmp = temp_reg_named('match')
    phi(tmp, typeof(m), phi_srcs)
    return tmp

def expr_attr(e, f):
    tx = express_typed(e)
    fieldptr = get_field_ptr(tx, f)
    return load(extrinsic(Name, f), typeof(f), fieldptr).xpr

def expr_lit(lit):
    return match(lit, ('IntLit(i)', lambda i: Const('%d' % (i,))),
                      ('FloatLit(f)', lambda f: Const('%f' % (f,))))

def get_strlit_ptr(var):
    tmp = temp_reg()
    out_xpr(tmp)
    out(' = getelementptr [%d x i8]* ' % (extrinsic(LiteralSize, var),))
    out_global_symbol(var)
    out(', i32 0, i32 0')
    newline()
    return tmp

def expr_tuplelit(lit, ts):
    tt = match(typeof(lit), "IPtr(tt==ITuple(_))")
    tmp = malloc(tt).xpr
    txs = map(express_typed, ts)
    struct = build_struct(tt, txs)
    store_xpr(struct, tmp)
    return tmp

def expr_listlit(lit, es):
    litt = typeof(lit)
    t = match(litt, "IPtr(IArray(0, t))")
    n = len(es)
    at = IArray(n + 1, t)
    xtmem = malloc(at)
    # Store length in first element
    lenx = TypedXpr(IInt(), Const(str(n)))
    if not itypes_equal(IInt(), t):
        lenx = cast(lenx, t)
    txs = map(express_typed, es)
    txs.insert(0, lenx)
    array = build_struct(at, txs)
    store_xpr(array, xtmem.xpr)
    # Return pointer to second element
    arr = get_element_ptr('listlit', xtmem, 1)
    return cast(TypedXpr(IPtr(t), arr), litt).xpr

def expr_with(var, expr):
    store_pat_var(var, TypedXpr(IVoidPtr(), Const('zeroinitializer')))
    return express(expr)

def expr_with_void(var, expr):
    store_pat_var(var, TypedXpr(IVoidPtr(), Const('zeroinitializer')))
    write_void_stmt(expr)

def express(expr):
    assert not env(LOCALS).unreachable, "Unreachable expr: %s" % (expr,)
    return match(expr,
        ('e==And(l, r)', expr_and),
        ('Bind(v)', LLVMBindable.express),
        ('e==Call(f, args)', expr_call),
        ('FuncExpr(f==Func(ps, body))', expr_func),
        ('e==InEnv(environ, init, expr)', expr_inenv),
        ('m==Match(p, cs)', expr_match),
        ('Attr(e, f)', expr_attr),
        ('e==Or(l, r)', expr_or),
        ('Lit(lit)', expr_lit),
        ('lit==TupleLit(es)', expr_tuplelit),
        ('lit==ListLit(es)', expr_listlit),
        ('e==Ternary(c, l, r)', expr_ternary),
        ('NullPtr()', lambda: Const("null")),
        ('WithVar(v, e)', expr_with))

def express_typed(expr):
    return TypedXpr(typeof(expr), express(expr))

def express_casted(expr):
    if not has_extrinsic(LLVMTypeCast, expr):
        assert not has_extrinsic(TypeCast, expr), "typecast not converted"
        return express_typed(expr)
    ex = express(expr)
    src, dest = extrinsic(LLVMTypeCast, expr)
    return cast(TypedXpr(src, ex), dest)

# PATTERN MATCHES

MatchState = DT('MatchState', ('failureBlock', Label))

MATCH = new_env('MATCH', MatchState)

def match_pat_ctor(pat, ctor, ps, tx):
    # XXX maybe codegen
    if Nullable.isMaybe(ctor):
        if extrinsic(Name, ctor) == 'Just':
            match_pat_just(pat, ps[0], tx)
        else:
            match_pat_nothing(pat, tx)
        return

    form = match(tx.type, "IPtr(IData(form))")
    layout = extrinsic(expand.DataLayout, form)
    if isJust(layout.discrimSlot):
        tx = cast(tx, IPtr(IData(ctor)))
        ixptr = get_element_ptr('ixptr', tx, fromJust(layout.discrimSlot))
        ix = load('ix', IInt(), ixptr)
        index = Const(str(extrinsic(expand.CtorIndex, ctor)))
        m = expr_binop('icmp eq', ix.xpr, index, ix.type)
        correctIx = new_label('got.' + extrinsic(Name, ctor), new_series(pat))
        br_cond(m, correctIx, env(MATCH).failureBlock)
        out_label(correctIx)

    datat = match(tx.type, "IPtr(t==IData(_))")
    ctorval = load(extrinsic(Name, ctor), datat, tx.xpr)

    for p, f in ezip(ps, ctor.fields):
        index = extrinsic(expand.FieldIndex, f)
        val = extractvalue(extrinsic(Name, f), ctorval, index)
        if has_extrinsic(LLVMTypeCast, p):
            src, dest = extrinsic(LLVMTypeCast, p)
            ptx = cast(TypedXpr(src, val), dest)
        else:
            assert not has_extrinsic(TypeCast, p), "pat cast not converted"
            ptx = TypedXpr(typeof(f), val)
        match_pat(p, ptx)

def match_pat_just(pat, p, tx):
    m = expr_binop('icmp ne', tx.xpr, Const('null'), tx.type)
    lbl = new_label('just', new_series(pat))
    br_cond(m, lbl, env(MATCH).failureBlock)
    out_label(lbl)
    match_pat(p, tx)

def match_pat_nothing(pat, tx):
    m = expr_binop('icmp eq', tx.xpr, Const('null'), tx.type)
    lbl = new_label('nothing', new_series(pat))
    br_cond(m, lbl, env(MATCH).failureBlock)
    out_label(lbl)

def match_pat_tuple(ps, tx):
    with_pat_tuple(ps, tx, match_pat)

def match_pat(pat, tx):
    match((pat, tx),
        ("(pat==PatCtor(c, ps), tx)", match_pat_ctor),
        ("(PatTuple(ps), tx)", match_pat_tuple),
        ("(PatVar(v), tx)", store_pat_var),
        ("(PatWild(), _)", nop))

# STATEMENTS

def write_assert(stmt, e, msg):
    ex = express(e)
    srs = new_series(stmt)
    pass_ = new_label('pass', srs)
    fail_ = new_label('fail', srs)
    br_cond(ex, pass_, fail_)
    out_label(fail_)
    m = express(msg)
    out('call void @fail(i8* %s) noreturn' % (xpr_str(m),))
    newline()
    out('unreachable')
    term()
    out_label(pass_)

def store_var(v, xpr):
    store_named(TypedXpr(typeof(v), xpr), v)

def store_attr(dest, f, val):
    tx = express_typed(dest)
    fieldptr = get_field_ptr(tx, f)
    store_xpr(TypedXpr(typeof(f), val), fieldptr)

def store_lhs(lhs, x):
    match(lhs,
        ('LhsVar(v)', lambda v: store_var(v, x)),
        ('LhsAttr(e, f)', lambda e, f: store_attr(e, f, x)))

def store_pat_var(v, txpr):
    out_name_reg(v)
    out(' = alloca ')
    out_t_nospace(txpr.type)
    newline()
    store_named(txpr, v)

def store_pat_tuple(ps, txpr):
    with_pat_tuple(ps, txpr, store_pat)

def with_pat_tuple(ps, txpr, func):
    # This silliness would disappear if we were using TypeOfs on the pats
    tupt, tts = match(txpr.type, ('IPtr(t==ITuple(tts))', tuple2))

    tupval = load('tuple', tupt, txpr.xpr)
    i = 0
    for p, tt in ezip(ps, tts):
        val = extractvalue('t%d' % (i,), tupval, i)
        i += 1
        func(p, TypedXpr(tt, val))

def store_pat(pat, txpr):
    # Really there ought to be TypeOfs on the pats rather than propagating
    # the typedxpr I think.
    match((pat, txpr), ('(PatVar(v), txpr)', store_pat_var),
                       ('(PatTuple(ps), txpr)', store_pat_tuple))

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

def write_break():
    begin, end = env(LOCALS).loopLabels
    br(end)

def write_continue():
    begin, end = env(LOCALS).loopLabels
    br(begin)

def write_cond(stmt, cs):
    n = len(cs)
    srs = new_series(stmt)
    csrs = new_series(cs[0])
    elif_ = Nothing()
    endif = new_label('endif', srs)
    for i, case in enumerate(cs):
        if isJust(elif_):
            out_label(fromJust(elif_))

        # Makeshift else
        if matches(case.test, "Bind(key('True'))"):
            assert i == n-1, "Dead cond case"
            out_comment('else:')
            write_body(case.body)
            continue # breaks, really

        if i == 0:
            out_comment('if %s:' % (stringify(case.test, 'Expr'),))
        else:
            out_pretty(case, 'CondCase(Expr)')
        ex = express(case.test)
        then = new_label('then', csrs)
        e = endif
        haveAnotherCase = False
        if i + 1 < n:
            haveAnotherCase = True
            csrs = new_series(cs[i + 1])
            e = new_label('elif', csrs)
            elif_ = Just(e)
        br_cond(ex, then, e)
        out_label(then)
        write_body(case.body)
        if haveAnotherCase and not env(LOCALS).unreachable:
            br(endif)
    if endif.used:
        out_label(endif)

def write_local_func_defn(f):
    assert has_extrinsic(expand.Closure, f)

def write_defn(pat, e):
    store_pat(pat, express_typed(e))

def write_field_specs(fields, layout):
    verbose = not env(DECLSONLY)
    if verbose:
        out('{')
        newline()
    else:
        out('{ ')

    specs = []
    if isJust(layout.extrSlot):
        assert fromJust(layout.extrSlot) == len(specs)
        specs.append((IVoidPtr(), "extrinsics"))
    if isJust(layout.discrimSlot):
        assert fromJust(layout.discrimSlot) == len(specs)
        specs.append((IInt(), "discrim"))
    for f in fields:
        assert extrinsic(expand.FieldIndex, f) == len(specs)
        specs.append((typeof(f), extrinsic(Name, f)))

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

def write_ctor(ctor, dt, layout):
    dtt = IPtr(IData(dt))
    out('declare ' if env(DECLSONLY) else 'define ')
    out_t(dtt)
    out_global_symbol(ctor)
    if env(DECLSONLY):
        write_param_types(map(typeof, ctor.fields))
        newline()
    else:
        as_local(lambda: _write_ctor_body(ctor, layout, dtt))
        out('}\n')

def _write_ctor_body(ctor, layout, dtt):
    txs = write_params(ctor.fields, map(typeof, ctor.fields))
    out(' {')
    newline()

    ctort = IData(ctor)
    inst = malloc(ctort)

    # Ought to sanity check slot indices here, but it's kind of awkward
    discrim = isJust(layout.discrimSlot)
    if discrim:
        index = extrinsic(expand.CtorIndex, ctor)
        txs.insert(0, TypedXpr(IInt(), Const(str(index))))

    if isJust(layout.extrSlot):
        txs.insert(0, TypedXpr(IVoidPtr(), Const("null")))

    struct = build_struct(ctort, txs)
    store_xpr(struct, inst.xpr)

    if discrim:
        inst = cast(inst, dtt)
    out('ret ')
    out_txpr(inst)
    term()

def write_dtstmt(form):
    layout = extrinsic(expand.DataLayout, form)
    if isJust(layout.discrimSlot):
        out_name_reg(form)
        out(' = type opaque')
        newline()
    for ctor in form.ctors:
        out_name_reg(ctor)
        out(' = type ')
        write_field_specs(ctor.fields, layout)
        newline()
        write_ctor(ctor, form, layout)
    if not env(DECLSONLY):
        newline()

def write_void_call(f, a):
    if matches(f, 'Bind(_)'):
        if LLVMBindable.express_called_void(f.target, a):
            return
    t = write_call(f, a, IVoid())
    assert isNothing(t)

def write_void_stmt(e):
    match(e,
        ('Call(f, a)', write_void_call),
        ('e==InEnv(environ, init, expr)', expr_inenv_void),
        ('WithVar(v, expr)', expr_with_void))

def write_expr_stmt(e):
    t = typeof(e)
    if matches(t, 'IVoid()'):
        write_void_stmt(e)
    else:
        express(e)

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
        out_t_nospace(t)
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
        tmp = temp_reg_named(extrinsic(Name, p))
        tx = TypedXpr(tp, tmp)
        out_txpr(tx)
        txs.append(tx)
    out(')')
    return txs

def write_top_func_decl(ref, tps, tret):
    out('declare ')
    out_t(tret)
    out_xpr(ref)
    write_param_types(tps)
    newline()

def write_top_func(var, f):
    tps, tret = match(extrinsic(LLVMTypeOf, f), ("IFunc(ps, ret)", tuple2))

    if env(DECLSONLY):
        write_top_func_decl(global_symbol(var), tps, tret)
        return
    elif env(EXPORTSYMS):
        out('define ')
    else:
        out('define internal ')
    out_t(tret)
    out_global_symbol(var)

    as_local(lambda: _write_top_func(f, f.params, f.body, tps, tret))
    out('}\n\n')

def _write_top_func(f, ps, body, tps, tret):
    txs = write_params(ps, tps)
    out(' {')
    newline()

    if len(ps) > 0:
        # write params to mem
        for p, tx in ezip(ps, txs):
            out_name_reg(p)
            out(' = alloca ')
            out_t(tx.type)
            newline()
            store_named(tx, p)
        newline()

    write_body(body)

    # Clean up
    last = env(LOCALS).currentBlock
    if last.used and last.needsTerminator:
        assert matches(tret, 'IVoid()'), "No terminator for non-void return?"
        out('ret void')
        term()

def write_return(expr):
    xt = express_typed(expr)
    out('ret ')
    out_txpr(xt)
    term()

def write_while(stmt, cond, body):
    srs = new_series(stmt)
    begin = new_label('while', srs)
    body_label = new_label('whilebody', srs)
    exit = new_label('endwhile', srs)

    # for break and continue
    old_labels = env(LOCALS).loopLabels
    env(LOCALS).loopLabels = (begin, exit)

    out_label(begin)
    ex = express(cond)
    br_cond(ex, body_label, exit)
    out_label(body_label)
    write_body(body)
    if not env(LOCALS).unreachable:
        br(begin)
    out_label(exit)

    env(LOCALS).loopLabels = old_labels

def write_stmt(stmt):
    out_pretty(stmt, 'Stmt(Expr)')
    match(stmt,
        ("stmt==Assert(e, m)", write_assert),
        ("Assign(lhs, e)", write_assign),
        ("AugAssign(op, lhs, e)", write_augassign),
        ("Break()", write_break),
        ("Continue()", write_continue),
        ("stmt==Cond(cs)", write_cond),
        ("Defn(PatVar(_), FuncExpr(f))", write_local_func_defn),
        ("Defn(pat, e)", write_defn),
        ("ExprStmt(e)", write_expr_stmt),
        ("Nop()", lambda: None),
        ("Return(e)", write_return),
        ("stmt==While(c, b)", write_while))

def write_body(body):
    map_(write_stmt, match(body, 'Body(ss)'))

def imported_bindable_used(v):
    return v in env(expand.IMPORTBINDS) or env(IR).overrideImportUsageCheck

def write_top_cdecl(v):
    if not imported_bindable_used(v):
        return
    tps, tret = match(extrinsic(LLVMTypeOf, v), ("IFunc(ps, ret)", tuple2))
    write_top_func_decl(global_symbol(v), tps, tret)

def write_top_var_func(v, f):
    if env(DECLSONLY) and not imported_bindable_used(v):
        return
    write_top_func(v, f)

def write_top_strlit(var, s):
    escaped, n = escape_strlit(s)
    add_extrinsic(LiteralSize, var, n)
    out_global_symbol(var)
    out(' = internal constant ')
    out(escaped)
    newline()

def escape_strlit(s):
    b = s.encode('utf-8')
    n = len(b) + 1
    lit = '[%d x i8] c"' % (n,)
    for c in iter(b):
        i = ord(c)
        lit += c if 31 < i < 127 else '\\%02x' % (i,)
    return (lit + '\\00"', n)

def write_top_lit(v, lit):
    if env(DECLSONLY) and not imported_bindable_used(v):
        return
    if matches(lit, "StrLit(_)"):
        write_top_strlit(v, lit.val)
        return
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

def as_local(f):
    lcl = setup_locals()
    in_env(LOCALS, lcl, f)
    assert not lcl.currentBlock.needsTerminator, "Last block not terminated?"

def write_unit(unit):
    for top in unit.funcs:
        in_env(EXPORTSYMS, True, lambda: write_top_func(top.var, top.func))

prelude = """; prelude
%Type = type opaque
%Env = type i8
%Extrinsic = type i8
declare void @fail(i8*) noreturn
declare void @match_fail() noreturn
declare i8* @malloc(i32)
; temp
declare i8* @_pushenv(%Env*, i8**, i8*)
declare void @_popenv(%Env*, i8*, i8*)

"""

def write_imports(dep):
    dt = match(dep.rootType, 'TData(dt, _)')
    if dt is extrinsic(FormSpec, DATATYPES['ModuleDecls']):
        out('; %s' % (extrinsic(Name, dep),))
        newline()
        in_env(DECLSONLY, True, lambda: write_top_decls(dep.root))

LLFile = new_extrinsic('LLFile', str, omni=True)
OFile = new_extrinsic('OFile', str, omni=True)

def write_ir(decl_mod, defn_mod, filename):
    def go():
        out(prelude)
        walk_deps(write_imports, defn_mod, set([decl_mod]))
        newline()
        out('; main')
        newline()
        def go():
            write_top_decls(decl_mod.root)
            write_unit(defn_mod.root)
        in_env(DECLSONLY, False, go)

    in_env(IR, setup_ir(filename),
        lambda: scope_extrinsic(LiteralSize,
        go))

    add_extrinsic(LLFile, decl_mod, filename)

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

def link(decl_mod, defn_mod, binary):
    objs = ['ir/z.o']

    def add_obj(dep):
        dt = dep.rootType.data
        if dt is extrinsic(FormSpec, DATATYPES['ModuleDecls']):
            if not has_extrinsic(OFile, dep):
                print col('Yellow', 'omitting missing'), extrinsic(Name, dep)
                return
            objs.append(extrinsic(OFile, dep))
    walk_deps(add_obj, defn_mod, set([decl_mod]))

    objs.append(extrinsic(OFile, decl_mod))
    return os.system('cc -o %s %s' % (binary, ' '.join(objs))) == 0

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
