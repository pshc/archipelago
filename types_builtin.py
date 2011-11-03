from base import *
from bedrock import List

def _type_tuple_equal(ts1, ts2):
    for t1, t2 in zip(ts1, ts2):
        if not type_equal(t1, t2):
            return False
    return True

def _type_func_equal(as1, r1, as2, r2):
    for a1, a2 in zip(as1, as2):
        if not type_equal(a1, a2):
            return False
    return type_equal(r1, r2)

def _type_apply_equal(t1, vs1, t2, vs2):
    if not type_equal(t1, t2):
        return False
    for v1, v2 in zip(vs1, vs2):
        if not type_equal(v1, v2):
            return False
    return True

def type_equal(a, b):
    if a is b:
        return True
    return match((a, b),
        ("(TMeta(a), b)", type_equal),
        ("(a, TMeta(b))", type_equal),
        ("(TVar(a), TVar(b))", lambda a, b: a is b),
        ("(TInt(), TInt())", lambda: True),
        ("(TStr(), TStr())", lambda: True),
        ("(TChar(), TChar())", lambda: True),
        ("(TBool(), TBool())", lambda: True),
        ("(TVoid(), TVoid())", lambda: True),
        ("(TTuple(ts1), TTuple(ts2))", _type_tuple_equal),
        ("(TAnyTuple(), TAnyTuple())", lambda: True),
        ("(TFunc(args1, r1), TFunc(args2, r2))", _type_func_equal),
        ("(TData(a), TData(b))", lambda: a is b),
        ("(TApply(t1, vs1), TApply(t2, vs2))", _type_apply_equal),
        ("_", lambda: False))

def _get_name(a):
    if not a or not has_extrinsic(Name, a):
        return '?? %r' % (a,)
    return extrinsic(Name, a)

REPR_ENV = None

def _meta_type_repr(t, j):
    assert t is not j
    return _type_repr(j)

def _type_repr(t):
    global REPR_ENV
    if t in REPR_ENV:
        return '<cyclic 0x%x>' % id(t)
    REPR_ENV.add(t)
    rstr = match(t, ("TVar(a)", _get_name),
                    ("t==TMeta(Just(j))", _meta_type_repr),
                    ("TMeta(Nothing())", lambda: '<bad meta>'),
                    ("TInt()", lambda: 'int'),
                    ("TStr()", lambda: 'str'),
                    ("TChar()", lambda: 'char'),
                    ("TBool()", lambda: 'bool'),
                    ("TVoid()", lambda: 'void'),
                    ("TTuple(ts)", lambda ts: '(%s)' %
                        (', '.join(_type_repr(t) for t in ts),)),
                    ("TAnyTuple()", lambda: 'tuple(*)'),
                    ("TFunc(s, r)", lambda s, r: '(%s)' %
                        (' -> '.join(_type_repr(t) for t in s + [r]),)),
                    ("TData(d)", _get_name),
                    ("TApply(t, vs)", lambda t, vs: '%s %s.' % (_type_repr(t),
                                '.'.join(map(_type_repr, vs)))),
                    ("_", lambda: '<bad type %s>' % type(t)))
    REPR_ENV.remove(t)
    return rstr

def _cyclic_check_type_repr(t):
    global REPR_ENV
    REPR_ENV = set()
    r = _type_repr(t)
    REPR_ENV = None
    return r

def _inject_type_reprs():
    temp = locals().copy()
    for t in temp:
        if len(t) > 1 and t[0] == 'T' and t[1].lower() != t[1]:
            temp[t].__repr__ = _cyclic_check_type_repr
_inject_type_reprs()

def map_type_vars(f, t):
    """Applies f to every typevar in the given type."""
    return match(t, ("tv==TVar(_)", f),
                    ("m==TMeta(r)", lambda m, r:
                        maybe(m, lambda r: map_type_vars(f, r), r)),
                    ("TFunc(args, ret)", lambda args, ret:
                        TFunc([map_type_vars(f, a) for a in args],
                              map_type_vars(f, ret))),
                    ("TTuple(ts)", lambda ts:
                        TTuple([map_type_vars(f, t) for t in ts])),
                    ("_", lambda: t))

Scheme = DT('Scheme', ('schemeVars', [Type]), ('schemeType', Type))

def _scheme_repr(s):
    begin = ':: '
    vs = s.schemeVars
    if vs:
        begin += ', '.join(map(_get_name, vs)) + ' => '
    return begin + repr(s.schemeType)
Scheme.__repr__ = _scheme_repr

# TODO
TDict = None
TList = TData(List)
TSet = None

TFile = None
THash = None

def _var(n): return TVar(n)

# Tuples are a shortcut for functions
builtins_types = {
    'fgetc': (TFile, TChar),
    'fputc': (TFile, TChar, TVoid),
    'fwrite': (TFile, TStr, TVoid),
    'fread': (TVoid, TInt, TInt, TFile, TVoid),
    'fopen': (TStr, TStr, TFile),
    'fclose': (TFile, TVoid),
    'sha256': (THash,),
    'sha256_hexdigest': (THash, TStr),
    'sha256_update': (THash, TStr, TVoid),

    'True': TBool, 'False': TBool,
    'ord': (TChar, TInt),
    '+': (TInt, TInt, TInt), '-': (TInt, TInt, TInt),
    '*': (TInt, TInt, TInt), '/': (TInt, TInt, TInt),
    '//': (TInt, TInt, TInt),
    'negate': (TInt, TInt),
    '==': (_var(1), _var(1), TBool), '!=': (_var(1), _var(1), TBool),
    '<': (TInt, TInt, TBool), '>': (TInt, TInt, TBool),
    '<=': (TInt, TInt, TBool), '>=': (TInt, TInt, TBool),
    'is': (_var(1), _var(1), TBool), 'is not': (_var(1), _var(1), TBool),
    'printf': (TStr, TAnyTuple, TVoid),
    '%': (TStr, TAnyTuple, TStr),
}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
