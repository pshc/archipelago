from base import *

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
        'IFunc', ('params', ['IType']), ('ret', 'IType'),
        'IPtr', ('type', 'IType'),
        'IVoidPtr')

LLVMTypeOf = new_extrinsic('LLVMTypeOf', IType)

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
        ("TData(dt, ts)", convert_dt),
        ("TArray(t)", lambda t: IPtr(IArray(0, convert_type(t)))),
        ("TTuple(ts)", lambda ts: IPtr(ITuple(map(convert_type, ts)))))

def convert_dt(dt, ts):
    # XXX maybe codegen
    if dt is extrinsic(FormSpec, DATATYPES['Maybe']):
        return convert_type(ts[0])
    return IPtr(IData(dt))

def i_DT(dt):
    return IData(extrinsic(FormSpec, SUPERS[dt]))

def itypes_equal(src, dest):
    same = lambda: True
    return match((src, dest),
        ('(IInt(), IInt())', same),
        ('(IInt64(), IInt64())', same),
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

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
