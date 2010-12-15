from base import *
from bedrock import Int, Str, Ref, List, maybe

Type, TVar, TMeta, TInt, TStr, TChar, TBool, TVoid, \
    TTuple, TAnyTuple, TFunc, TData, TApply \
    = ADT('Type',
        'TVar', ('varAtom', 'Atom'),
        'TMeta', ('metaType', 'Maybe(Type)'),
        'TInt', 'TStr', 'TChar', 'TBool',
        'TVoid',
        'TTuple', ('tupleTypes', ['Type']),
        'TAnyTuple',
        'TFunc', ('funcArgs', ['Type']), ('funcRet', 'Type'),
        'TData', ('dataAtom', 'Atom'),
        'TApply', ('appType', 'Type'), ('appVars', ['Type']))

def _get_name(a):
    return match(a, ("named(nm)", lambda nm: nm))

def _meta_type_repr(t, j):
    assert t is not j
    return _type_repr(j)

def _type_repr(t):
    return match(t, ("TVar(a)", _get_name),
                    ("t==TMeta(Just(j))", _meta_type_repr),
                    ("TInt()", lambda: 'int'),
                    ("TStr()", lambda: 'str'),
                    ("TChar()", lambda: 'char'),
                    ("TBool()", lambda: 'bool'),
                    ("TVoid()", lambda: 'void'),
                    ("TTuple(ts)", lambda ts: '(%s)' % ', '.join(_type_repr(t)
                                                                 for t in ts)),
                    ("TAnyTuple()", lambda: 'tuple(*)'),
                    ("TFunc(s, r)", lambda s, r: ' -> '.join(_type_repr(t)
                                                        for t in s + [r])),
                    ("TData(d)", _get_name),
                    ("TApply(t, vs)", lambda t, vs: '%s %s.' % (_type_repr(t),
                                '.'.join(map(_type_repr, vs)))))

_temp = locals().copy()
for _t in _temp:
    if _t[0:1] == 'T':
        _temp[_t].__repr__ = _type_repr

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

def _var(n): return TVar(Int(n, []))

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
    # etc to tuple5
    'True': TBool, 'False': TBool,
    'ord': (TChar, TInt),
    'identity': (_var(1), _var(1)),
    'tuple2': (_var(1), _var(2), TTuple([_var(1), _var(2)])),

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
