from base import *
from atom import *

LExpr, L, CallIndirect, Cast, FuncVal, NullPtr, Undefined, WithVar = \
    ADT(('LExpr', Expr),
        'CallIndirect', ('func', 'LExpr'), ('args', ['LExpr']),
                        ('envParam', bool),
        'Cast', ('src', 'IType'), ('dest', 'IType'), ('expr', 'LExpr'),
        'FuncVal', ('funcVar', '*GlobalVar'), ('ctx', 'Maybe(*Var)'),
        'NullPtr',
        'Undefined',
        'WithVar', ('var', Var), ('expr', 'LExpr'))

ExpandedUnit = DT('ExpandedUnit', ('funcs', ['TopFunc(LExpr)']))

IFuncMeta = DT('IFuncMeta', ('noReturn', bool))

IType, IInt, IInt64, IFloat, IBool, IVoid, \
    IArray, ITuple, IData, IFunc, IPtr, IVoidPtr = ADT('IType',
        'IInt',
        'IInt64',
        'IFloat',
        'IBool',
        'IVoid',
        'IArray', ('count', int), ('type', 'IType'),
        'ITuple', ('types', ['IType']),
        'IData', ('datatype', '*DataType'),
        'IFunc', ('params', ['IType']), ('ret', 'IType'), ('meta', IFuncMeta),
        'IPtr', ('type', 'IType'),
        'IVoidPtr')

LLVMTypeOf = new_extrinsic('LLVMTypeOf', IType)
LLVMPatCast = new_extrinsic('LLVMPatCast', (IType, IType))

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
        ("TFunc(tps, result, meta)", _convert_func),
        ("TData(dt, _)", lambda dt: IPtr(IData(dt))),
        ("TArray(t)", lambda t: IPtr(IArray(0, convert_type(t)))),
        ("TTuple(ts)", lambda ts: IPtr(ITuple(map(convert_type, ts)))))

def _convert_func(tps, result, meta):
    ips = map(convert_type, tps)
    if meta.envParam:
        ips.append(IVoidPtr())
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
               all(itypes_equal(a, b) for a, b in ezip(m.ps1, m.ps2)) and \
               itypes_equal(m.r1, m.r2)
    else:
        return False

def i_ADT(dt):
    return IPtr(IData(extrinsic(FormSpec, dt)))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
