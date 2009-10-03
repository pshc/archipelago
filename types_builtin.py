from base import *

Type, TVar, TInt, TStr, TChar, TBool, TVoid, TNullable, \
    TTuple, TAnyTuple, TFunc \
    = ADT('Type',
        'TVar', ('varIndex', int),
        'TInt', 'TStr', 'TChar', 'TBool',
        'TVoid',
        'TNullable', ('nullType', 'Type'),
        'TTuple', ('tupleTypes', ['Type']),
        'TAnyTuple',
        'TFunc', ('funcArgs', ['Type']), ('funcRet', 'Type'))

def map_type_vars(f, t, data):
    """Applies f to every typevar('s index) in the given type."""
    return match(t, ("TVar(n)", lambda n: f(n, data)),
                    ("TNullable(v)", lambda v:
                        TNullable(map_type_vars(f, v, data))),
                    ("TFunc(args, ret)", lambda args, ret:
                        TFunc([map_type_vars(f, a, data) for a in args],
                              map_type_vars(f, ret, data))),
                    ("TTuple(ts)", lambda ts:
                        TTuple([map_type_vars(f, t, data) for t in ts])),
                    ("_", lambda: t))

Scheme = DT('Scheme', ('schemeVars', [Type]), ('schemeType', Type))

# TODO
TDict = None
TList = None
TSet = None

TFile = None
THash = None

# Special: array, sizeof, hint, stringify, to_atom, to_void, getattr, range,
#          object

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
    'dict_keys': (TDict, TList),
    'set_add': (TSet, TSet, TVoid),
    'list_append': (TList, TVar(1), TVoid),
    'list_sort': (TList, TVoid),
    'identity': (TVar(1), TVar(1)),
    'tuple2': (TVar(1), TVar(2), TTuple([TVar(1), TVar(2)])),
    # etc to tuple5
    'None': TNullable(TVar(1)),
    'True': TBool, 'False': TBool,
    'ord': (TChar, TInt),
    'len': (TList, TInt),
    'set': (TList, TSet),

    '+': (TInt, TInt, TInt), '-': (TInt, TInt, TInt),
    '*': (TInt, TInt, TInt), '/': (TInt, TInt, TInt),
    '//': (TInt, TInt, TInt),
    '%': (TStr, TAnyTuple, TStr),
    'negate': (TInt, TInt),
    '==': (TVar(1), TVar(1), TBool), '!=': (TVar(1), TVar(1), TBool),
    '<': (TInt, TInt, TInt), '>': (TInt, TInt, TInt),
    '<=': (TInt, TInt, TInt), '>=': (TInt, TInt, TInt),
    'is': (TVar(1), TVar(1), TBool), 'is not': (TVar(1), TVar(1), TBool),
    'in': (TVar(1), TList, TBool), 'not in': (TVar(1), TList, TBool),
    'slice': (TList, TInt, TInt, TList),
    'print': (TStr, TVoid),
}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
