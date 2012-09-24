from base import *

def prim_equal(p1, p2):
    return match((p1, p2),
        ("(PInt(), PInt())", lambda: True),
        ("(PFloat(), PFloat())", lambda: True),
        ("(PStr(), PStr())", lambda: True),
        ("(PChar(), PChar())", lambda: True),
        ("(PBool(), PBool())", lambda: True),
        ("_", lambda: False))

def _type_tuple_equal(ts1, ts2):
    if len(ts1) != len(ts2):
        return False
    for t1, t2 in ezip(ts1, ts2):
        if not type_equal(t1, t2):
            return False
    return True

def _type_func_equal(as1, r1, m1, as2, r2, m2):
    if len(as1) != len(as2):
        return False
    for a1, a2 in ezip(as1, as2):
        if not type_equal(a1, a2):
            return False
    if not type_equal(r1, r2):
        return False
    return metas_equal(m1, m2)

def _type_data_equal(d1, ts1, d2, ts2):
    if d1 is not d2:
        return False
    if len(ts1) != len(ts2):
        return False
    for t1, t2 in ezip(ts1, ts2):
        if not type_equal(t1, t2):
            return False
    return True

def type_equal(a, b):
    if a is b:
        return True
    return match((a, b),
        ("(TVar(a), TVar(b))", lambda a, b: a is b),
        ("(TPrim(a), TPrim(b))", prim_equal),
        ("(TVoid(), TVoid())", lambda: True),
        ("(TTuple(ts1), TTuple(ts2))", _type_tuple_equal),
        ("(TFunc(args1, r1, m1), TFunc(args2, r2, m2))", _type_func_equal),
        ("(TData(d1, ts1), TData(d2, ts2))", _type_data_equal),
        ("(TArray(a), TArray(b))", type_equal),
        ("(TWeak(a), TWeak(b))", type_equal),
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
                    ("TPrim(PInt())", lambda: 'int'),
                    ("TPrim(PStr())", lambda: 'str'),
                    ("TPrim(PChar())", lambda: 'char'),
                    ("TPrim(PBool())", lambda: 'bool'),
                    ("TVoid()", lambda: 'void'),
                    ("TTuple(ts)", lambda ts: '(%s)' %
                        (', '.join(_type_repr(t) for t in ts),)),
                    ("TFunc(s, r, _)", lambda s, r: '(%s)' %
                        (' -> '.join(_type_repr(t) for t in s + [r]),)),
                    ("TData(d, [])", _get_name),
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
                    ("TData(dt, ts)", lambda dt, ts:
                        TData(dt, [map_type_vars(f, t) for t in ts])),
                    ("TFunc(args, ret, meta)", lambda args, ret, meta:
                        TFunc([map_type_vars(f, a) for a in args],
                              map_type_vars(f, ret), copy_meta(meta))),
                    ("TTuple(ts)", lambda ts:
                        TTuple([map_type_vars(f, t) for t in ts])),
                    ("TArray(t)", lambda t: TArray(map_type_vars(f, t))),
                    ("TWeak(t)", lambda t: TWeak(map_type_vars(f, t))),
                    ("_", lambda: t))

def visit_type_vars(f, t):
    visit = lambda t: visit_type_vars(f, t)
    visit_many = lambda ts: all(visit_type_vars(f, t) for t in ts)
    return match(t, ("TVar(tv)", f),
                    ("TData(_, ts)", visit_many),
                    ("TFunc(args, ret, _)", lambda args, ret:
                        visit_many(args) and visit(ret)),
                    ("TTuple(ts)", visit_many),
                    ("TArray(t)", visit),
                    ("TWeak(t)", visit),
                    ("_", lambda: True))


def occurs(typeVar, t):
    return not visit_type_vars(lambda tv: tv is not typeVar, t)

def subst_affects(mapping, t):
    return not visit_type_vars(lambda tv: tv not in mapping, t)

def subst(mapping, t):
    return map_type_vars(lambda st: mapping.get(st.typeVar, st), t)

# Make sure the input is sane and non-redundant
def checked_subst(mapping, t):
    for tvar, rt in mapping.iteritems():
        assert not occurs(tvar, rt), "%s occurs in replacement %s" % (tvar, rt)
    unseen = set(mapping)
    assert len(unseen) > 0, "Empty substitution for %s" % (t,)
    def app(st):
        tvar = st.typeVar
        if tvar in mapping:
            st = mapping[tvar]
            if tvar in unseen:
                unseen.remove(tvar)
        return st
    s = map_type_vars(app, t)
    assert len(unseen) == 0, "Typevars %s unused in subst for %s" % (unseen, t)
    return s

builtins_types = {
    'True': 'bool', 'False': 'bool', 'not': 'bool -> bool',
    '+': '(int, int) -> int', '-': '(int, int) -> int',
    '*': '(int, int) -> int', '//': '(int, int) -> int',
    '%': '(int, int) -> int',
    'negate': 'int -> int', 'fnegate': 'float -> float',
    'fadd': '(float, float) -> float', 'fsub': '(float, float) -> float',
    'fmul': '(float, float) -> float', 'fdiv': '(float, float) -> float',
    'float': 'int -> float', 'int': 'float -> int',
    '&': '(int, int) -> int', '|': '(int, int) -> int',
    '^': '(int, int) -> int',
    '==': '(int, int) -> bool', '!=': '(int, int) -> bool',
    '<': '(int, int) -> bool', '>': '(int, int) -> bool',
    '<=': '(int, int) -> bool', '>=': '(int, int) -> bool',
    'is': '(a, a) -> bool', 'is not': '(a, a) -> bool',
    'len': '[a] -> int', 'subscript': '([a], int) -> a',
    'buffer': 'int -> str',
}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
