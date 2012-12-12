from base import *
from atom import *

LExpr, L, CallIndirect, Cast, FuncVal, NullPtr, AttrIx, SizeOf, Undefined = \
    ADT(('LExpr', Expr),
        'CallIndirect', ('func', 'LExpr'), ('args', ['LExpr']),
                        ('envParam', bool),
        'Cast', ('src', 'IType'), ('dest', 'IType'), ('expr', 'LExpr'),
        'FuncVal', ('funcVar', '*GlobalVar'), ('ctx', 'Maybe(*Var)'),
        'NullPtr',
        'AttrIx', ('expr', 'LExpr'),
        'SizeOf', ('type', 'IType'),
        'Undefined')

ExpandedUnit = DT('ExpandedUnit', ('funcs', ['TopFunc(LExpr)']))


Block = DT('Block', ('label', str),
                    ('stmts', ['Stmt(LExpr)']),
                    ('nullOuts', ['*Var']),
                    ('terminator', 'Terminator'),
                    ('entryBlocks', ['*Block']))

Terminator, TermJump, TermJumpCond, TermReturnNothing, TermReturn, \
    TermUnreachable = ADT('Terminator',
    'TermJump', ('dest', 'Maybe(*Block)'),
    'TermJumpCond', ('expr', LExpr),
                    ('trueDest', 'Maybe(*Block)'),
                    ('falseDest', 'Maybe(*Block)'),
    'TermReturnNothing',
    'TermReturn', ('expr', LExpr),
    'TermUnreachable')

Register = DT('Register')

@impl(Bindable, Register)
def isLocalVar_Register(reg):
    return True

LLocal, LVar, LRegister = ADT('BlockParam',
    'LVar', ('var', Var),
    'LRegister', ('register', Register))

BlockFunc = DT('BlockFunc', ('var', '*GlobalVar'),
                            ('gcVars', ['*Var']),
                            ('params', [LLocal]),
                            ('blocks', [Block]))

BlockUnit = DT('BlockUnit', ('funcs', [BlockFunc]))

CtorIndex = new_extrinsic('CtorIndex', int)
FieldIndex = new_extrinsic('FieldIndex', int)

IFuncMeta = DT('IFuncMeta', ('noReturn', bool))

IType, IInt, IInt64, IFloat, IBool, IVoid, IArray, ITuple, \
    IData, IDataCtor, IFunc, IPtr, IWeak, IVoidPtr = ADT('IType',
        'IInt',
        'IInt64',
        'IFloat',
        'IBool',
        'IVoid',
        'IArray', ('count', int), ('type', 'IType'),
        'ITuple', ('types', ['IType']),
        'IData', ('datatype', '*DataType'),
        'IDataCtor', ('ctor', '*Ctor'),
        'IFunc', ('params', ['IParam']), ('ret', 'IType'), ('meta', IFuncMeta),
        'IPtr', ('type', 'IType'),
        'IWeak', ('type', 'IType'),
        'IVoidPtr')

IParam = DT('IParam', ('type', IType),
                      ('held', bool))

LLVMTypeOf = new_extrinsic('LLVMTypeOf', IType)
LLVMPatCast = new_extrinsic('LLVMPatCast', (IType, IType))

def is_strong_ptr(t):
    return matches(t, "IPtr(_) or IVoidPtr() or IArray(_, _)")

def types_punned(a, b):
    # Determines whether two non-equal types convert to identical ITypes
    assert not type_equal(a, b)
    punny = lambda: True
    # TODO: TFunc
    return match((a, b),
        ("(TVar(_), TVar(_))", punny),
        ("(TPrim(PStr()), TVar(_))", punny),
        ("(TVar(_), TPrim(PStr()))", punny),
        ("(TData(d1, _), TData(d2, _))", lambda d1, d2:
                d1 == d2 and not type_equal(a, b)),
        ("(TArray(t1), TArray(t2))", types_punned),
        ("(TTuple(a), TTuple(b))", tuples_punned),
        ("_", lambda: False))

def tuples_punned(a, b):
    # We need at least one pun (and the rest equal)
    pun = False
    for t1, t2 in ezip(a, b):
        if not type_equal(t1, t2):
            if types_punned(a, b):
                pun = True
            else:
                return False
    return pun

def convert_type(t):
    return match(t,
        ("TPrim(PInt())", IInt),
        ("TPrim(PFloat())", IFloat),
        ("TPrim(PBool())", IBool),
        ("TPrim(PStr())", IVoidPtr),
        ("TVar(_)", IVoidPtr),
        ("TFunc(pts, result, meta)", _convert_func),
        ("TData(dt, _)", lambda dt: IPtr(IData(dt))),
        ("TCtor(ctor, _)", lambda ctor: IPtr(IDataCtor(ctor))),
        ("TArray(t)", lambda t: IPtr(IArray(0, convert_type(t)))),
        ("TTuple(ts)", lambda ts: IPtr(ITuple(map(convert_type, ts)))),
        ("TWeak(t)", lambda t: IWeak(convert_type(t))))

def _convert_func(pts, result, meta):
    ips = []
    for pt, pmeta in ezip(pts, meta.params):
        ips.append(IParam(convert_type(pt), pmeta.held))
    if meta.envParam:
        ips.append(IParam(IVoidPtr(), False))
    meta = IFuncMeta(False)
    m = match(result)
    if m('Ret(t)'):
        res = convert_type(m.t)
    elif m('Void()'):
        res = IVoid()
    elif m('Bottom()'):
        res = IVoid()
        meta.noReturn = True
    return ITuple([IFunc(ips, res, meta), IVoidPtr()])

def convert_func_type(t):
    fval = match(t, ("TFunc(ps, res, m)", _convert_func))
    return fval.types[0]

def itypes_equal(src, dest):
    m = match((src, dest))
    if m('(IInt(), IInt())'):
        return True
    elif m('(IVoidPtr(), IVoidPtr())'):
        return True
    elif m('(IPtr(a), IPtr(b))'):
        return itypes_equal(m.a, m.b)
    elif m('(IInt64(), IInt64())'):
        return True
    elif m('(IFloat(), IFloat())'):
        return True
    elif m('(IBool(), IBool())'):
        return True
    elif m('(IVoid(), IVoid())'):
        return True
    elif m('(IArray(n1, t1), IArray(n2, t2))'):
        return m.n1 == m.n2 and itypes_equal(m.t1, m.t2)
    elif m('(ITuple(ts1), ITuple(ts2))'):
        return all(itypes_equal(a, b) for a, b in ezip(m.ts1, m.ts2))
    elif m('(IFunc(ps1, r1, _), IFunc(ps2, r2, _))'):
        return len(m.ps1) == len(m.ps2) and \
               all(iparams_equal(a, b) for a, b in ezip(m.ps1, m.ps2)) and \
               itypes_equal(m.r1, m.r2)
    else:
        return False

def iparams_equal(src, dest):
    if not itypes_equal(src, dest):
        return False
    if src.held != dest.held:
        return False
    return True

def i_ADT(dt):
    return IPtr(IData(extrinsic(FormSpec, dt)))

IRComments = new_extrinsic('IRComments', [str])

def copy_type(dest, src):
    # bleh... vat?
    add_extrinsic(LLVMTypeOf, dest, extrinsic(LLVMTypeOf, src))

def cast(src, dest, e):
    assert not itypes_equal(src, dest), "%s already of %s type" % (e, src)
    casted = Cast(src, dest, e)
    add_extrinsic(LLVMTypeOf, casted, dest)
    return casted

def cast_from_voidptr(e, t):
    return match(t, ('IVoidPtr()', lambda: e),
                    ('_', lambda: cast(IVoidPtr(), t, e)))

def cast_to_voidptr(e, t):
    return match(t, ('IVoidPtr()', lambda: e),
                    ('_', lambda: cast(t, IVoidPtr(), e)))

def runtime_call(name, args):
    f = RUNTIME[name]
    ft = extrinsic(LLVMTypeOf, f)
    bind = L.Bind(f)
    add_extrinsic(LLVMTypeOf, bind, ft)
    call = L.Call(bind, args)
    add_extrinsic(LLVMTypeOf, call, ft.ret)
    return call

def runtime_void_call(name, args):
    f = RUNTIME[name]
    bind = L.Bind(f)
    copy_type(bind, f)
    return S.VoidStmt(VoidCall(bind, args))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
