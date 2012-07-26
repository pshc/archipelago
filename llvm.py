from atom import *
import expand
import os
import sys

Label = DT('Label', ('name', str),
                    ('used', bool),
                    ('needsTerminator', bool))

IRInfo = DT('IRInfo', ('stream', None))
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
    return IRInfo(stream)

def setup_locals():
    entry = Label(':entry:', True, True)
    return IRLocals(False, False, 0, entry, entry, set(), Nothing())

IType, IInt, IFloat, IBool, IVoid, \
    IArray, ITuple, IData, IFunc, IPtr, IVoidPtr = ADT('IType',
        'IInt',
        'IFloat',
        'IBool',
        'IVoid',
        'IArray', ('count', int), ('type', 'IType'),
        'ITuple', ('types', ['IType']),
        'IData', ('datatype', '*DataType'),
        'IFunc', ('params', ['IType']), ('ret', 'IType'),
        'IPtr', ('type', 'IType'),
        'IVoidPtr')

TypedXpr = DT('TypedXpr', ('type', IType), ('xpr', 'Xpr'))

Xpr, Reg, Tmp, Global, ConstStruct, Const, ConstOp, ConstCast = ADT('Xpr',
        'Reg', ('label', 'str'), ('index', 'int'),
        'Tmp', ('index', 'int'),
        'Global', ('name', str),
        'ConstStruct', ('vals', [TypedXpr]),
        'Const', ('frag', 'str'),
        'ConstOp', ('op', 'str'), ('args', [TypedXpr]),
        'ConstCast', ('kind', str), ('src', TypedXpr), ('dest', IType))

def is_const(x):
    return match(x,
        ('Reg(_, _)', lambda: False), ('Tmp(_)', lambda: False),
        ('Global(_)', lambda: True), ('ConstStruct(_)', lambda: True),
        ('Const(_)', lambda: True), ('ConstOp(_, _)', lambda: True))

Replacement = new_extrinsic('Replacement', Xpr)

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

def func_ref(f):
    if not has_extrinsic(Name, f):
        add_extrinsic(Name, f, "unnamed_func")
    return global_ref(f)

def global_ref(v):
    return Global(extrinsic(Name, v))

def out_func_ref(f):
    out_xpr(func_ref(f))

def out_global_ref(v):
    out_xpr(global_ref(v))

def newline():
    if have_env(LOCALS):
        imm_out('\n')
        env(LOCALS).needIndent = True
    else:
        out('\n')

def comma():
    out(', ')

# FUNCTION-LOCAL OUTPUT

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
                    ('ConstCast(kind, src, dest)', constcast_str))

def txpr_str(txpr):
    return '%s %s' % (t_str(txpr.type), xpr_str(txpr.xpr))

def constop_str(f, args):
    return '%s (%s)' % (f, ', '.join(map(txpr_str, args)))

def conststruct_str(vals):
    return '{ %s }' % (', '.join(map(txpr_str, vals)),)

def constcast_str(kind, src, dest):
    return '%s (%s to %s)' % (kind, txpr_str(src), t_str(dest))

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
    sizeof = temp_reg_named('sizeof')
    sizeoft = IInt()
    out_xpr(sizeof)
    out(' = ptrtoint ')
    out_t_ptr(t)
    out('getelementptr')
    nullx = TypedXpr(IPtr(t), Const("null"))
    write_args([nullx, TypedXpr(IInt(), Const("1"))])
    out(' to ')
    out_t_nospace(sizeoft)
    newline()
    f = func_ref(runtime_decl('malloc'))
    mem = call(IVoidPtr(), f, [TypedXpr(IInt(), sizeof)])
    return cast(mem, IPtr(t))

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

def get_element_ptr(tmp, tx, index):
    out_xpr(tmp)
    out(' = getelementptr ')
    out_txpr(tx)
    comma()
    out('i32 0')
    comma()
    out('i32 %d' % (index,))
    newline()

def get_field_ptr(tx, f):
    tmp = temp_reg_named(extrinsic(Name, f))
    get_element_ptr(tmp, tx, extrinsic(expand.FieldIndex, f))
    return tmp

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

def cast(txpr, dest):
    src = txpr.type
    if matches((src, dest), '(IVoidPtr(), IVoidPtr())'):
        return txpr
    assert not itypes_equal(src, dest), "Pointless %s cast to itself" % (src,)
    kind = match((src, dest),
        ('(IInt() or IBool(), IVoidPtr())', lambda: 'inttoptr'),
        ('(IVoidPtr(), IInt() or IBool())', lambda: 'ptrtoint'),
        ('(IVoidPtr() or IPtr(_), IVoidPtr() or IPtr(_))', lambda: 'bitcast'),
        ('(IInt(), IFloat())', lambda: 'bitcast'),
        ('(IFloat(), IInt())', lambda: 'bitcast'),
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

_cached_runtime_refs = {}
def runtime_decl(name):
    # "Proper" impl of this module will just point at the decls directly
    ref = _cached_runtime_refs.get(name)
    if ref is not None:
        return ref
    runtime = loaded_modules['runtime']
    from astconv import loaded_module_export_names, cNamespace
    symbolTable = loaded_module_export_names[runtime]
    ref = symbolTable[(name, cNamespace)]
    _cached_runtime_refs[name] = ref
    return ref

# TYPES

def convert_type(t):
    return match(t,
        ("TPrim(PInt())", IInt),
        ("TPrim(PFloat())", IFloat),
        ("TPrim(PBool())", IBool),
        ("TPrim(PStr())", IVoidPtr),
        ("TVoid()", IVoid),
        ("TVar(_)", IVoidPtr),
        ("TFunc(ps, r)", lambda ps, r:
                         IFunc(map(convert_type, ps), convert_type(r))),
        ("TData(dt, _)", lambda dt: IPtr(IData(dt))),
        ("TArray(t)", lambda t: IPtr(IArray(0, convert_type(t)))),
        ("TTuple(ts)", lambda ts: IPtr(ITuple(map(convert_type, ts)))))

def itypes_equal(src, dest):
    same = lambda: True
    return match((src, dest),
        ('(IInt(), IInt())', same),
        ('(IFloat(), IFloat())', same),
        ('(IBool(), IBool())', same),
        ('(IVoid(), IVoid())', same),
        ('(IVoidPtr(), IVoidPtr())', same),
        ('(IArray(n1, t1), IArray(n2, t2))', lambda n1, t1, n2, t2:
            n1 == n2 and itypes_equal(t1, t2)),
        ('(ITuple(ts1), ITuple(ts2))', lambda ts1, ts2:
            all(itypes_equal(a, b) for a, b in ezip(ts1, ts2))),
        ('(IFunc(ps1, r1), IFunc(ps2, r2))', lambda ps1, r1, ps2, r2:
            len(ps1) == len(ps2) and
            all(itypes_equal(a, b) for a, b in ezip(ps1, ps2)) and
            itypes_equal(r1, r2)),
        ('(IPtr(a), IPtr(b))', itypes_equal),
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

def convert_split_tfunc(t):
    return match(t,
        ('TFunc(p, r)', lambda p, r: (map(convert_type, p), convert_type(r))))

def t_str(t):
    return match(t,
        ("IInt()", lambda: "i32"),
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
                         lambda target, args: Nothing()))

@impl(LLVMBindable, Builtin)
def express_Builtin(b):
    return match(b,
        ('key("True")', lambda: Const('true')),
        ('key("False")', lambda: Const('false')))

@impl(LLVMBindable, Var)
def express_Var(v):
    if has_extrinsic(Replacement, v):
        return extrinsic(Replacement, v)
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
    return func_ref(c)

def una_op(b):
    # grr boilerplate
    return match(b,
        ('key("not")', lambda: 'not'),
        ('key("negate")', lambda: 'negate'),
        ('key("fnegate")', lambda: 'fnegate'),
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

def expr_unary(op, arg):
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
    decl = runtime_decl(name)

    fx = func_ref(decl)
    if matches(rett, "IVoid()"):
        call_void(fx, argxs)
        return Nothing()

    tmp = call(rett, fx, argxs)
    return Just(tmp)

def expr_call(e, f, args):
    if matches(f, 'Bind(_)'):
        mret = LLVMBindable.express_called(f.target, args)
        if isJust(mret):
            return fromJust(mret)
    return fromJust(write_call(f, args, typeof(e))).xpr

@impl(LLVMBindable, Builtin)
def express_called_Builtin(target, args):
    op = una_op(target)
    if op != '':
        assert len(args) == 1, '%s is unary' % (op,)
        arg = express_typed(args[0])
        return Just(expr_unary(op, arg))
    else:
        op = bin_op(target)
        assert len(args) == 2, '%s requires two args' % (op,)
        left = express(args[0])
        right = express(args[1])
        return Just(expr_binop(op, left, right, typeof(args[0])))

def expr_func(f, ps, body):
    clos = extrinsic(expand.Closure, f)
    assert not clos.isClosure, "TODO"
    return func_ref(clos.func)

def env_type(environ):
    return ITuple([convert_type(environ.type), IBool()])

def read_env_state(environ, index, regname):
    tmp = load('env', env_type(environ), global_ref(environ))
    return extractvalue(regname, tmp, index)

def expr_getenv(environ):
    return read_env_state(environ, 0, extrinsic(Name, environ))

def expr_haveenv(environ):
    return read_env_state(environ, 1, 'have.%s' % (extrinsic(Name, environ)))

def env_setup(environ, init):
    name = extrinsic(Name, environ)
    t = env_type(environ)
    envref = global_ref(environ)

    out('; push env %s' % (name,))
    newline()
    old = load('old.%s' % (name,), t, envref)
    i = express(init)
    envt = match(t, "ITuple([envt, IBool()])")
    info = ConstStruct([TypedXpr(envt, i), TypedXpr(IBool(), Const('true'))])
    store_xpr(TypedXpr(t, info), envref)
    return old

def env_teardown(environ, old):
    out('; pop env %s' % (extrinsic(Name, environ),))
    newline()
    store_xpr(old, global_ref(environ))

def expr_inenv(environ, init, e):
    old = env_setup(environ, init)
    ret = express(e)
    env_teardown(environ, old)
    return ret

def expr_inenv_void(environ, init, e):
    old = env_setup(environ, init)
    write_void_stmt(e)
    env_teardown(environ, old)

def expr_getextrinsic(extr, e, exists):
    sym = '_hasextrinsic' if exists else '_getextrinsic'
    extrx = TypedXpr(IVoidPtr(), global_ref(extr))
    t = IBool() if exists else convert_type(extr.type)
    ex = express_casted(e)
    return fromJust(write_runtime_call(sym, [extrx, ex], t)).xpr

def expr_scopeextrinsic(extr, e):
    out('; enter %s' % (extrinsic(Name, extr),))
    newline()
    ret = express(e)
    out('; exit %s' % (extrinsic(Name, extr),))
    newline()
    return ret

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
    return load(extrinsic(Name, f), convert_type(f.type), fieldptr).xpr

def expr_strlit(lit):
    info = extrinsic(expand.ExpandedDecl, lit)
    tmp = temp_reg()
    out_xpr(tmp)
    out(' = getelementptr [%d x i8]* ' % (extrinsic(LiteralSize, info.var),))
    out_global_ref(info.var)
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
    arr = temp_reg_named('listlit')
    get_element_ptr(arr, xtmem, 1)
    return cast(TypedXpr(IPtr(t), arr), litt).xpr

def express(expr):
    assert not env(LOCALS).unreachable, "Unreachable expr: %s" % (expr,)
    return match(expr,
        ('e==And(l, r)', expr_and),
        ('Bind(v)', LLVMBindable.express),
        ('e==Call(f, args)', expr_call),
        ('FuncExpr(f==Func(ps, body))', expr_func),
        ('GetEnv(environ)', expr_getenv),
        ('HaveEnv(environ)', expr_haveenv),
        ('InEnv(environ, init, e)', expr_inenv),
        ('GetExtrinsic(x, e)', lambda x, e: expr_getextrinsic(x, e, False)),
        ('HasExtrinsic(x, e)', lambda x, e: expr_getextrinsic(x, e, True)),
        ('ScopeExtrinsic(extr, e)', expr_scopeextrinsic),
        ('m==Match(p, cs)', expr_match),
        ('Attr(e, f)', expr_attr),
        ('e==Or(l, r)', expr_or),
        ('IntLit(i)', lambda i: Const('%d' % (i,))),
        ('FloatLit(f)', lambda f: Const('%f' % (f,))),
        ('lit==StrLit(_)', expr_strlit),
        ('lit==TupleLit(es)', expr_tuplelit),
        ('lit==ListLit(es)', expr_listlit),
        ('e==Ternary(c, l, r)', expr_ternary))

def express_typed(expr):
    return TypedXpr(typeof(expr), express(expr))

def express_casted(expr):
    if not has_extrinsic(TypeCast, expr):
        return express_typed(expr)
    ex = express(expr)
    src, dest = extrinsic(TypeCast, expr)
    return cast(TypedXpr(convert_type(src), ex), convert_type(dest))

# PATTERN MATCHES

MatchState = DT('MatchState', ('failureBlock', Label))

MATCH = new_env('MATCH', MatchState)

def match_pat_ctor(pat, ctor, ps, tx):
    form = match(tx.type, "IPtr(IData(form))")
    layout = extrinsic(expand.DataLayout, form)
    if isJust(layout.discrimSlot):
        tx = cast(tx, IPtr(IData(ctor)))
        ixptr = temp_reg()
        get_element_ptr(ixptr, tx, fromJust(layout.discrimSlot))
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
        if has_extrinsic(TypeCast, p):
            # DT instantiation affects this field
            src, dest = extrinsic(TypeCast, p)
            ptx = cast(TypedXpr(convert_type(src), val), convert_type(dest))
        else:
            ptx = TypedXpr(convert_type(f.type), val)
        match_pat(p, ptx)

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
    store_xpr(TypedXpr(convert_type(f.type), val), fieldptr)

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

def write_cond(stmt, cs, else_):
    n = len(cs)
    haveElse = isJust(else_)
    srs = new_series(stmt)
    csrs = new_series(cs[0])
    elif_ = Nothing()
    else_label = Just(new_label('else', srs)) if haveElse else Nothing()
    endif = new_label('endif', srs)
    for i, case in enumerate(cs):
        if isJust(elif_):
            out_label(fromJust(elif_))
        ex = express(case.test)
        then = new_label('then', csrs)
        e = endif
        haveAnotherCase = True
        if i + 1 < n:
            csrs = new_series(cs[i + 1])
            e = new_label('elif', csrs)
            elif_ = Just(e)
        elif haveElse:
            e = fromJust(else_label)
        else:
            haveAnotherCase = False
        br_cond(ex, then, e)
        out_label(then)
        write_body(case.body)
        if haveAnotherCase and not env(LOCALS).unreachable:
            br(endif)
    if haveElse:
        out_label(fromJust(else_label))
        write_body(fromJust(else_))
    if endif.used:
        out_label(endif)

def check_static_replacement(v, f):
    if has_extrinsic(Replacement, v):
        return True
    if has_extrinsic(expand.VarUsage, v):
        if extrinsic(expand.VarUsage, v).isReassigned:
            return False
    add_extrinsic(Replacement, v, func_ref(f))
    return True

def write_func_defn(v, e, f):
    if not check_static_replacement(v, f):
        write_defn(v, e)

def write_defn(pat, e):
    store_pat(pat, express_typed(e))

def write_field_specs(fields, layout):
    verbose = not env(DECLSONLY)
    if verbose:
        out('{')
        newline()
    else:
        out('{ ')

    specs = [(convert_type(f.type), extrinsic(Name, f)) for f in fields]
    if isJust(layout.discrimSlot):
        assert fromJust(layout.discrimSlot) == 1
        specs.insert(0, (IInt(), "discrim"))
    if isJust(layout.extrSlot):
        assert fromJust(layout.extrSlot) == 0
        specs.insert(0, (IVoidPtr(), "extrinsics"))

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
    out_func_ref(ctor)
    fts = [convert_type(f.type) for f in ctor.fields]
    if env(DECLSONLY):
        write_param_types(fts)
        newline()
    else:
        as_local(lambda: _write_ctor_body(ctor, layout, dtt, fts))
        out('}\n')

def _write_ctor_body(ctor, layout, dtt, fts):
    txs = write_params(ctor.fields, fts)
    out(' {')
    newline()

    ctort = IData(ctor)
    inst = malloc(ctort)

    discrim = isJust(layout.discrimSlot)
    if discrim:
        assert fromJust(layout.discrimSlot) == 1
        index = extrinsic(expand.CtorIndex, ctor)
        txs.insert(0, TypedXpr(IInt(), Const(str(index))))

    if isJust(layout.extrSlot):
        assert fromJust(layout.extrSlot) == 0
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
    t = write_call(f, a, IVoid())
    assert isNothing(t)

def write_void_stmt(e):
    match(e,
        ('Call(f, a)', write_void_call),
        ('InEnv(environ, init, e)', expr_inenv_void))

def write_expr_stmt(e):
    t = typeof(e)
    if matches(t, 'IVoid()'):
        write_void_stmt(e)
    else:
        express(e)

def write_new_env(e):
    decl = env(DECLSONLY)
    out_global_ref(e)
    out(' = %sglobal ' % ('external ' if decl else '',))
    out_t_nospace(env_type(e))
    if not decl:
        out(' zeroinitializer')
    newline()

def write_new_extrinsic(extr):
    decl = env(DECLSONLY)
    out_global_ref(extr)
    out(' = %sglobal i8' % ('external ' if decl else '',))
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

def write_top_func(f):
    tps, tret = convert_split_tfunc(extrinsic(TypeOf, f))

    if env(DECLSONLY):
        write_top_func_decl(func_ref(f), tps, tret)
        return
    elif env(EXPORTSYMS):
        out('define ')
    else:
        out('define internal ')
    out_t(tret)
    out_func_ref(f)

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
    begin = new_label('loop', srs)
    body_label = new_label('body', srs)
    exit = new_label('exit', srs)

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

def write_writeextrinsic(extr, node, val, isNew):
    sym = '_addextrinsic' if isNew else '_updateextrinsic'
    extrx = TypedXpr(IVoidPtr(), global_ref(extr))
    n = express_casted(node)
    v = express_casted(val)
    r = write_runtime_call(sym, [extrx, n, v], IVoid())
    assert isNothing(r)

def write_stmt(stmt):
    match(stmt,
        ("stmt==Assert(e, m)", write_assert),
        ("Assign(lhs, e)", write_assign),
        ("AugAssign(op, lhs, e)", write_augassign),
        ("Break()", write_break),
        ("Continue()", write_continue),
        ("stmt==Cond(cs, else_)", write_cond),
        ("Defn(PatVar(v), e==FuncExpr(f))", write_func_defn),
        ("Defn(pat, e)", write_defn),
        ("ExprStmt(e)", write_expr_stmt),
        ("Return(e)", write_return),
        ("stmt==While(c, b)", write_while),
        ("WriteExtrinsic(extr, node, val, isNew)", write_writeextrinsic))

def write_body(body):
    map_(write_stmt, match(body, 'Body(ss)'))

def write_top_cdecl(v):
    if not env(DECLSONLY):
        check_static_replacement(v, v)
        tps, tret = convert_split_tfunc(extrinsic(TypeOf, v))
        write_top_func_decl(global_ref(v), tps, tret)
    else:
        write_top_func(v)

def write_top_var_func(v, f):
    if not env(DECLSONLY):
        check_static_replacement(v, f)
    write_top_func(f)

def write_top_strlit(var, s):
    escaped, n = escape_strlit(s)
    add_extrinsic(LiteralSize, var, n)
    out_global_ref(var)
    out(' = internal constant %s' % (escaped,))
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
        ("TopCDecl(v)", write_top_cdecl),
        ("TopDefn(PatVar(v), FuncExpr(f))", write_top_var_func),
        ("TopDT(form)", write_dtstmt),
        ("TopEnv(environ)", write_new_env),
        ("TopExtrinsic(extr)", write_new_extrinsic))

def as_local(f):
    lcl = setup_locals()
    in_env(LOCALS, lcl, f)
    assert not lcl.currentBlock.needsTerminator, "Last block not terminated?"

def write_unit(unit):
    for top in unit.tops:
        if has_extrinsic(expand.Expansion, top):
            for ex in extrinsic(expand.Expansion, top):
                in_env(EXPORTSYMS, False, lambda: match(ex,
                    ("ExStrLit(var, s)", write_top_strlit),
                    ("ExSurfacedFunc(f)", write_top_func)))
            newline()
        in_env(EXPORTSYMS, True, lambda: write_top(top))

def write_unit_decls(unit):
    map_(write_top, unit.tops)

prelude = """; prelude
%Type = type opaque
declare void @fail(i8*) noreturn
declare void @match_fail() noreturn

"""

def write_imports(dep):
    dt = match(dep.rootType, 'TData(dt, _)')
    if dt is extrinsic(FormSpec, DATATYPES['CompilationUnit']):
        out('; %s' % (extrinsic(Name, dep),))
        newline()
        in_env(DECLSONLY, True, lambda: write_unit_decls(dep.root))

LLFile = new_extrinsic('LLFile', str)
OFile = new_extrinsic('OFile', str)

def write_ir(mod, filename):
    def go():
        out(prelude)
        runtime = loaded_modules['runtime']
        if runtime is not None:
            write_imports(runtime)

        walk_deps(write_imports, mod)
        newline()
        out('; main')
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

def link(mod, binary):
    objs = ['ir/z.o']

    def add_obj(dep):
        dt = dep.rootType.data
        if dt is extrinsic(FormSpec, DATATYPES['CompilationUnit']):
            if not has_extrinsic(OFile, dep):
                print col('Yellow', 'omitting missing'), extrinsic(Name, dep)
                return
            objs.append(extrinsic(OFile, dep))
    walk_deps(add_obj, mod)

    objs.append(extrinsic(OFile, mod))
    return os.system('cc -o %s %s' % (binary, ' '.join(objs))) == 0

def in_llvm_env(func):
    captures = {}
    extrs = [LLFile, OFile]
    return capture_scoped(extrs, captures, func)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
