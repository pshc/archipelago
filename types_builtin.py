from base import *

def prim_equal(p1, p2):
    return match((p1, p2),
        ("(PInt(), PInt())", lambda: True),
        ("(PFloat(), PFloat())", lambda: True),
        ("(PStr(), PStr())", lambda: True),
        ("(PChar(), PChar())", lambda: True),
        ("(PBool(), PBool())", lambda: True),
        ("_", lambda: False))

def array_kinds_equal(k1, k2):
    return match((k1, k2),
        ("(AGC(), AGC())", lambda: True),
        ("(ABoxed(), ABoxed())", lambda: True),
        ("(ARaw(), ARaw())", lambda: True),
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
    if not results_equal(r1, r2):
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

def _type_array_equal(t1, k1, t2, k2):
    if not type_equal(t1, t2):
        return False
    if not array_kinds_equal(k1, k2):
        return False
    return True

def type_equal(a, b):
    if a is b:
        return True
    return match((a, b),
        ("(TVar(a), TVar(b))", lambda a, b: a is b),
        ("(TPrim(a), TPrim(b))", prim_equal),
        ("(TTuple(ts1), TTuple(ts2))", _type_tuple_equal),
        ("(TFunc(args1, r1, m1), TFunc(args2, r2, m2))", _type_func_equal),
        ("(TData(d1, ts1), TData(d2, ts2))", _type_data_equal),
        ("(TCtor(c1, ts1), TCtor(c2, ts2))", _type_data_equal),
        ("(TArray(t1, k1), TArray(t2, k2))", _type_array_equal),
        ("(TWeak(a), TWeak(b))", type_equal),
        ("_", lambda: False))

def results_equal(a, b):
    return match((a, b), ("(Ret(a), Ret(b))", type_equal),
                         ("(Void(), Void())", lambda: True),
                         ("(Bottom(), Bottom())", lambda: True),
                         ("_", lambda: False))

def _get_name(a):
    if not a or not has_extrinsic(Name, a):
        try:
            return '<%r?>' % (a,)
        except:
            return '<??!>'
    return extrinsic(Name, a)

REPRENV = new_env('REPRENV', set([Type]))

def _meta_type_repr(t, j):
    assert t is not j
    return _type_repr(j)

def _type_repr(t):
    seen = env(REPRENV)
    if t in seen:
        return '<cyclic 0x%x>' % id(t)
    seen.add(t)
    rstr = match(t, ("TVar(v)", lambda v: col('Green', _get_name(v))),
                    ("TPrim(PInt())", lambda: 'int'),
                    ("TPrim(PFloat())", lambda: 'float'),
                    ("TPrim(PStr())", lambda: 'str'),
                    ("TPrim(PChar())", lambda: 'char'),
                    ("TPrim(PBool())", lambda: 'bool'),
                    ("TTuple(ts)", lambda ts: fmtcol('^Cyan^t(^N{0}^Cyan)^N',
                        (col('Cyan', ', ').join(map(_type_repr, ts))))),
                    ("TArray(t, kind)", _tarray_repr),
                    ("TFunc(ps, res, m)", _func_repr),
                    ("TData(d, ps)", _tdata_repr),
                    ("TCtor(c, ps)", _tdata_repr),
                    ("TWeak(t)", lambda t: '*%s' % (_type_repr(t),)),
                    ("CMeta(cell)", repr),
                    ("_", lambda: mark('<bad type %s>' % type(t))))
    seen.remove(t)
    return rstr

def _func_repr(ps, result, meta):
    if len(ps) == 0:
        s = 'void'
    elif len(ps) == 1 and not meta.params[0].held:
        s = _type_repr(ps[0])
    else:
        bits = [col('Cyan', '(')]
        first = True
        for param, pmeta in ezip(ps, meta.params):
            if first:
                first = False
            else:
                bits.append(col('Cyan', ', '))
            bits.append(_type_repr(param))
            if pmeta.held:
                bits.append(col('LG', ' held'))
        bits.append(col('Cyan', ')'))
        s = ''.join(bits)
    ret = match(result, ('Ret(t)', _type_repr),
                        ('Void()', lambda: 'void'),
                        ('Bottom()', lambda: 'noreturn'))
    if not meta.envParam:
        ret += col('LG', ' noenv')
    for environ in meta.requiredEnvs:
        ret += fmtcol(' ^LG{0}^N', extrinsic(Name, environ))
    return fmtcol('{0} ^Cyan->^N {1}', s, ret)

def _tdata_repr(dt, apps):
    if not apps:
        return _get_name(dt)
    return fmtcol('{0}^LG(^N{1}^LG)^N', dt,
            col('Cyan', ', ').join(map(_type_repr, apps)))

def _tarray_repr(t, kind):
    pfx = match(kind, ("AGC()", lambda: ''),
                      ("ABoxed()", lambda: 'x'),
                      ("ARaw()", lambda: 'r'))
    return fmtcol('^Red{0}^N[{1}]', pfx, _type_repr(t))

def cyclic_check_type_repr(t):
    return in_env(REPRENV, set(), lambda: _type_repr(t))

def _inject_type_reprs():
    temp = globals()
    for t in temp:
        if len(t) > 1 and t[0] == 'T' and t[1].isupper():
            temp[t].__repr__ = cyclic_check_type_repr
_inject_type_reprs()

def map_type_vars(f, t):
    """Applies f to every typevar in the given type."""
    # critical function
    cls = t.__class__
    if cls is TPrim:
        return t
    elif cls is TVar:
        return f(t)
    elif cls is TData:
        return TData(t.data, [map_type_vars(f, a) for a in t.appTypes])
    elif cls is TCtor:
        return TCtor(m.ctor, [map_type_vars(f, a) for a in t.appTypes])
    elif cls is TFunc:
        ps = [map_type_vars(f, p) for p in t.paramTypes]
        m = match(t.result)
        if m('Ret(t)'):
            m.ret(Ret(map_type_vars(f, m.t)))
        elif m('Void()'):
            m.ret(Void())
        elif m('Bottom()'):
            m.ret(Bottom())
        return TFunc(ps, m.result(), copy_meta(t.meta))
    elif cls is TTuple:
        return TTuple([map_type_vars(f, tt) for tt in t.tupleTypes])
    elif cls is TArray:
        return TArray(map_type_vars(f, t.elemType), t.arrayKind)
    elif cls is TWeak:
        return TWeak(map_type_vars(f, t.refType))
    else:
        assert False

def occurs(typeVar, t):
    visit = lambda t: visit_type_vars(f, t)
    visit_many = lambda ts: all(visit_type_vars(f, t) for t in ts)
    cls = t.__class__
    if cls is TPrim:
        return False
    elif cls is TVar:
        return t.typeVar is typeVar
    elif cls is TData or cls is TCtor:
        return any(occurs(typeVar, a) for a in t.appTypes)
    elif cls is TFunc:
        if any(occurs(typeVar, p) for p in t.paramTypes):
            return True
        if t.result.__class__ is Ret and occurs(typeVar, t.result.type):
            return True
        return False
    elif cls is TTuple:
        return any(occurs(typeVar, tt) for tt in t.tupleTypes)
    elif cls is TArray:
        return occurs(typeVar, t.elemType)
    elif cls is TWeak:
        return occurs(typeVar, t.refType)
    else:
        assert False

def subst_affects(mapping, t):
    visit = lambda t: visit_type_vars(f, t)
    visit_many = lambda ts: all(visit_type_vars(f, t) for t in ts)
    cls = t.__class__
    if cls is TPrim:
        return False
    elif cls is TVar:
        return t.typeVar in mapping
    elif cls is TData or cls is TCtor:
        return any(subst_affects(mapping, a) for a in t.appTypes)
    elif cls is TFunc:
        if any(subst_affects(mapping, p) for p in t.paramTypes):
            return True
        if t.result.__class__ is Ret and subst_affects(mapping, t.result.type):
            return True
        return False
    elif cls is TTuple:
        return any(subst_affects(mapping, tt) for tt in t.tupleTypes)
    elif cls is TArray:
        return subst_affects(mapping, t.elemType)
    elif cls is TWeak:
        return subst_affects(mapping, t.refType)
    else:
        assert False

def app_map(data, appTs):
    apps = {}
    for tv, at in ezip(data.tvars, appTs):
        if isinstance(at, TVar) and at.typeVar is tv:
            continue
        apps[tv] = at
    return apps

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

def is_strong_type(t):
    return matches(t, "TData(_, _) or TCtor(_, _) or TArray(_, _)" +
            " or TTuple(_) or TFunc(_, _, _)")

def ctor_type(ctor, dtT):
    paramTypes = []
    paramMetas = []
    for f in ctor.fields:
        paramTypes.append(f.type)
        paramMetas.append(ParamMeta(is_strong_type(f.type)))
    return TFunc(paramTypes, Ret(dtT), basic_meta(paramMetas))

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
    'rawlen': 'r[a] -> int', 'intsubscript': '(r[int], int) -> int',
    'buffer': 'int -> str', 'free_buffer': 'str -> void',
}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
