import compiler
from types import FunctionType

DATATYPES = {}
CTORS = {}

class Structured(object):
    pass

_deferred_type_parses = []

def _make_ctor(name, members, superclass):
    invariant = None
    if members and isinstance(members[-1], FunctionType):
        invariant = members.pop()
    mems = [(nm) for (nm, t) in members]
    slots = ', '.join(map(repr, mems) + ['"_ix"'])
    args = ''.join(', %s' % m for m in mems)
    ix = len(DATATYPES)
    stmts = ''.join(['    self.%s = %s\n' % (m, m) for m in mems])
    if invariant:
        stmts += '    assert self.check_invariant(), "Invariant failure"\n'
    code = """class %(name)s(superclass):
  __slots__ = [%(slots)s]
  __types__ = []
  def __init__(self%(args)s, **_tvars):
    self._ix = %(ix)d
%(stmts)s""" % locals()
    exec code
    ctor = CTORS[name] = eval(name)
    for nm, t in members:
        ctor.__types__.append(t)
    if invariant:
        ctor.check_invariant = invariant
    return ctor

def DT(*members):
    members = list(members)
    name = members.pop(0)
    exec 'class %s(Structured): ctors = []' % (name,)
    t = eval(name)
    ctor = _make_ctor(name, members, t)
    t.ctors.append(ctor)
    ctor.__dt__ = t
    t.__form__ = _dt_form(t)
    DATATYPES[name] = t
    return ctor

def ADT(*ctors):
    ctors = list(ctors)
    tname = ctors.pop(0)
    exec 'class %s(Structured): ctors = []' % (tname,)
    t = eval(tname)
    data = [t]
    ctor_ix = 0
    while ctors:
        ctor = ctors.pop(0)
        members = []
        while ctors and not isinstance(ctors[0], basestring):
            members.append(ctors.pop(0))
        d = _make_ctor(ctor, members, t)
        d.__module__ = tname
        d._ctor_ix = ctor_ix
        d.__dt__ = t
        ctor_ix += 1
        t.ctors.append(d)
        data.append(d)
    _dt_form(t)
    DATATYPES[tname] = t
    return tuple(data)

def _dt_form(dt):
    pass

# Envs

EnvInfo = DT('EnvInfo', ('envName', str), ('envType', 'Type'),
                        ('envStack', '[a]'))

_ENVS = set()

def new_env(name, t):
    assert isinstance(name, basestring)
    if t is not None:
        t = parse_type(t)
    e = EnvInfo(name, t, [])
    _ENVS.add(e)
    return e

def in_env(e, initial, func):
    stack = e.envStack
    stack.append(initial)
    count = len(stack)
    ret = func()
    assert len(stack) == count, 'Imbalanced env %s stack' % e.envName
    stack.pop()
    return ret

def env(e):
    assert len(e.envStack), 'Not in env %s at present' % e.envName
    return e.envStack[-1]

def have_env(e):
    return bool(e.envStack)

def display_envs(verbose=False):
    for e in _ENVS:
        if e.envStack:
            print col('Purple', e.envName + ':')
            if verbose:
                for s in e.envStack:
                    print repr(s)
            else:
                print repr(e.envStack[-1])

# stupid debugger shortcut
class DumpEnvs(object):
    def __repr__(self):
        display_envs()
        return '<DumpEnvs>'
dumpenvs = DumpEnvs()

TVARS = new_env('TVARS', None)
NEWTYPEVARS = new_env('NEWTYPEVARS', None)

# Extrinsics

ExtInfo = DT('ExtInfo', ('label', str), ('t', 'Type'), ('stack', [{'a': 't'}]),
                        ('captures', [{'a': 't'}]))

# Omnipresent for now
Name = ExtInfo('Name', str, [{}], [])
FormBacking = ExtInfo('FormBacking', object, [{}], [])

def new_extrinsic(label, t):
    if t is not None:
        t = parse_type(t)
    return ExtInfo(label, t, [], [])

def extrinsic(ext, obj):
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    record = ext.stack[-1]
    assert obj in record, '%r has no %s' % (obj, ext.label)
    return record[obj]

def scope_extrinsic(ext, func):
    new = ext.stack[-1].copy() if len(ext.stack) else {}
    ext.stack.append(new)
    ret = func()
    n = ext.stack.pop()
    assert n is new, "Extrinsic stack imbalance"
    return ret

def capture_extrinsic(ext, cap, func):
    assert isinstance(cap, dict)
    ext.captures.append(cap)
    ret = func()
    off = ext.captures.pop()
    assert off is cap, "Imbalanced capture"
    return ret

def capture_scoped(exts, captures, func):
    def step(f, ext):
        captures[ext] = {}
        return lambda: scope_extrinsic(ext,
                lambda: capture_extrinsic(ext, captures[ext], f))
    return reduce(step, exts, func)()

def in_extrinsic_scope(ext):
    return bool(ext.stack)

def add_extrinsic(ext, obj, val):
    assert not isinstance(obj, value_types), "%s on value %r" % (ext.label,obj)
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    map = ext.stack[-1]
    assert obj not in map, "%r already has %s extrinsic" % (obj, ext.label)
    map[obj] = val
    if len(ext.captures) > 0:
        cap = ext.captures[-1]
        assert obj not in cap
        cap[obj] = val

def update_extrinsic(ext, obj, val):
    assert not isinstance(obj, value_types), "%s on value %r" % (ext.label,obj)
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    map = ext.stack[-1]
    assert obj in map, "%r doesn't have %s extrinsic yet" % (obj, ext.label)
    map[obj] = val
    if len(ext.captures) > 0:
        cap = ext.captures[-1]
        assert obj in cap
        cap[obj] = val

def has_extrinsic(ext, obj):
    assert not isinstance(obj, value_types), "%s on value %r" % (ext.label,obj)
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    return obj in ext.stack[-1]

value_types = (basestring, bool, int, float, tuple, type(None))

# Forms

Field = DT('Field', ('type', 'Type'))
Ctor = DT('Ctor', ('fields', [Field]))
DataType = DT('DataType', ('ctors', [Ctor]), ('tvars', ['TypeVar']))

del _dt_form

def _ctor_form(ctor):
    fields = []
    for nm, t in zip(ctor.__slots__, ctor.__types__):
        if _deferred_type_parses is None:
            t = in_env(NEWTYPEVARS, None, lambda: parse_type(t))
        field = Field(t)
        add_extrinsic(Name, field, nm)
        fields.append(field)
    form = Ctor(fields)
    add_extrinsic(Name, form, ctor.__name__)
    add_extrinsic(FormBacking, form, ctor)
    ctor.__form__ = form
    del ctor.__types__
    if _deferred_type_parses is not None:
        _deferred_type_parses.append(form)
    return form

def _dt_form(dt):
    tvs = {}
    ctors = in_env(TVARS, tvs, lambda: map(_ctor_form, dt.ctors))
    form = DataType(ctors, tvs.values())
    add_extrinsic(Name, form, dt.__name__)
    add_extrinsic(FormBacking, form, dt)
    dt.__form__ = form
    return form

def _restore_forms():
    for ctor in CTORS.itervalues():
        _dt_form(DATATYPES[ctor.__name__])
_restore_forms()

# Type representations

TypeVar = DT('TypeVar')

PrimType, PInt, PStr, PChar, PBool = ADT('PrimType',
        'PInt', 'PStr', 'PChar', 'PBool')

Type, TVar, TPrim, TVoid, \
    TTuple, TAnyTuple, TFunc, TData, TApply, TArray, TWeak \
    = ADT('Type',
        'TVar', ('typeVar', '*TypeVar'),
        'TPrim', ('primType', PrimType),
        'TVoid',
        'TTuple', ('tupleTypes', ['Type']),
        'TAnyTuple',
        'TFunc', ('funcArgs', ['Type']), ('funcRet', 'Type'),
        'TData', ('data', '*DataType'),
        'TApply', ('appTarget', 'Type'), ('appVar', '*TypeVar'),
                                         ('appArg', 'Type'),
        'TArray', ('elemType', 'Type'),
        'TWeak', ('refType', 'Type'))

def TInt():
    return TPrim(PInt())
def TBool():
    return TPrim(PBool())
def TStr():
    return TPrim(PStr())
def TChar():
    return TPrim(PChar())

_parsed_type_cache = {}

def parse_new_type(t, tvars):
    return in_env(NEWTYPEVARS, None, lambda:
            in_env(TVARS, tvars, lambda: parse_type(t)))

def parse_type(t):
    if type(t) is type and issubclass(t, Structured):
        form = t.__form__
        if isinstance(form, Ctor):
            form = t.__dt__.__form__
        return TData(form)
    elif isinstance(t, basestring):
        key = t.replace('->', '>').replace('*', '-')
        t = _parsed_type_cache.get(key)
        if not t:
            t = compiler.parse(key, mode='eval').node
            _parsed_type_cache[key] = t
        return realize_type(t)
    elif t is int:
        return TInt()
    elif t is str:
        return TStr()
    elif t is bool:
        return TBool()
    elif t is None:
        return TVoid()
    elif isinstance(t, tuple):
        return TTuple(map(parse_type, t))
    elif isinstance(t, list):
        assert len(t) == 1
        return TArray(parse_type(t[0]))
    elif isinstance(t, set):
        assert len(t) == 1
        return _apply_set_type(parse_type(list(t)[0]))
    elif isinstance(t, dict):
        assert len(t) == 1
        [(key, val)] = t.iteritems()
        return _apply_dict_type(parse_type(key), parse_type(val))
    elif t is type or t is object or t is file:
        # MAGIC!
        return t
    assert False, "Unknown type repr of type %r: %r" % (type(t), t)

types_by_name = dict(str=TStr, int=TInt, bool=TBool, void=TVoid)

def realize_type(t):
    ast = compiler.ast
    if isinstance(t, ast.CallFunc):
        if isinstance(t.node, ast.Name) and t.node.name == 't':
            return TTuple(map(realize_type, t.args))
        assert len(t.args) == 1
        dt = realize_type(t.node)
        tvar = 'a'
        if not isinstance(dt, TForward):
            tvar = dt.data.tvars[0]
        return TApply(dt, tvar, realize_type(t.args[0]))
    elif isinstance(t, ast.Compare):
        tuplify = lambda x: x.nodes if isinstance(x, ast.Tuple) else [x]
        ops = [tuplify(t.expr)]
        for o, e in t.ops[:-1]:
            assert o == '>'
            ops.insert(0, tuplify(e))
        # Don't tuplify the last one (final result)
        o, e = t.ops[-1]
        assert o == '>'
        r = realize_type(e)
        def step(r, ts):
            params = map(realize_type, ts)
            if len(params) == 1 and matches(params[0], 'TVoid()'):
                params = []
            return TFunc(params, r)
        return reduce(step, ops, r)
    elif isinstance(t, ast.List):
        assert len(t.nodes) == 1
        return TArray(realize_type(t.nodes[0]))
    elif isinstance(t, ast.Tuple):
        return TTuple(map(realize_type, t.nodes))
    elif isinstance(t, ast.Name):
        t = t.name
        if len(t) == 1:
            tvars = env(TVARS)
            tvar = tvars.get(t)
            if tvar is None:
                assert have_env(NEWTYPEVARS), "Tried to create TypeVar %s" % t
                tvar = TypeVar()
                add_extrinsic(Name, tvar, t)
                tvars[t] = tvar
            return TVar(tvar)
        elif t in DATATYPES:
            return TData(DATATYPES[t].__form__)
        elif t in types_by_name:
            return types_by_name[t]()
        else:
            return TForward(t)
    elif isinstance(t, ast.UnarySub):
        return TWeak(realize_type(t.expr))
    assert False, "Unknown type ast repr: %r" % (t,)

TForward = DT('TForward', ('name', str))

def t_DT(dt):
    return TData(dt.__dt__.__form__)

def _apply_list_type(t):
    listT = parse_type('List')
    return TApply(listT, 'a', t)

def _apply_set_type(t):
    setT = parse_type('Set')
    return TApply(setT, 'a', t)

def _apply_dict_type(k, v):
    dictT = parse_type('Dict')
    keyVar, valVar = 'k', 'v'
    if not isinstance(dictT, TForward):
        keyVar = dictT.data.tvars[0]
        valVar = dictT.data.tvars[1]
    return TApply(TApply(dictT, valVar, v), keyVar, k)

# Parse the types in TypeVar, Type fields
def _parse_deferred():
    global _deferred_type_parses
    for ctor in _deferred_type_parses:
        def parse():
            for field in ctor.fields:
                field.type = parse_type(field.type)
        tvars = {}
        in_env(NEWTYPEVARS, None, lambda: in_env(TVARS, tvars, parse))
        ctor.__dt__.tvars = tvars.values()
    _deferred_type_parses = None
_parse_deferred()

# Global options

GenOpts = DT('GenOpts', ('quiet', bool), ('color', None), ('dumpTypes', bool))
GENOPTS = new_env('GENOPTS', GenOpts)

import re
_col_re = re.compile(r'\^(\w+)\^?')
del re
_col_shorts = {'N': 'Normal', 'DG': 'DarkGray'}

def col(c, s):
    colors = env(GENOPTS).color
    if colors:
        c = _col_shorts.get(c, c)
        s = '%s%s%s' % (getattr(colors, c), s, colors.Normal)
    return s

def fmtcol(s, *args):
    colors = env(GENOPTS).color
    if colors:
        def colorize(m):
            c = m.group(1)
            c = _col_shorts.get(c, c)
            return getattr(colors, c)
        s = _col_re.sub(colorize, s)
    else:
        s = _col_re.sub('', s)
    return s.format(*args)

def mark(s):
    return col('Red', s)

# Pretty printing
# (naive quadratic version)

PrettyPrinted = new_extrinsic('PrettyPrinted', None)

def pretty_brief(name, o):
    if name == 'Bind':
        o = o.binding
        name = type(o).__name__
        pb = pretty_brief(name, o)
        if pb is not None:
            return "'%s" % (pb,)

    if name == 'BindBuiltin':
        return col('Yellow', extrinsic(Name, o.builtin))
    elif name == 'BindCtor':
        return fmtcol('^Brown{0}^N', extrinsic(Name, o.ctor))
    elif name == 'BindVar':
        return repr(o.var)
    elif name == 'IntLit':
        return col('Cyan', 'i%d' % (o.val,))
    elif name == 'StrLit':
        return fmtcol('^Cyan^s{0!r}^N', o.val)
    elif name == 'TPrim' or name == 'CPrim':
        return col('Cyan', repr(o.primType))
    elif name == 'TupleLit':
        return 't%r' % (tuple(o.vals),)
    elif name == 'DataType':
        return col('Brown', extrinsic(Name, o))
    return None

def _id(o):
    return fmtcol('^DG@x{0:x}^N', id(o) % 0xfffff)

def __repr__(o):
    if not in_extrinsic_scope(PrettyPrinted):
        return scope_extrinsic(PrettyPrinted, lambda: repr(o))
    t = type(o)
    name = t.__name__
    if has_extrinsic(PrettyPrinted, o):
        if has_extrinsic(Name, o):
            name = fmtcol('{0} ^Green"{1}"^N', name, extrinsic(Name, o))
        return '<%s %s>' % (name, _id(o))
    add_extrinsic(PrettyPrinted, o, None)

    brief = pretty_brief(name, o)
    if brief is not None:
        return brief
    if has_extrinsic(Name, o):
        name = fmtcol('{0} ^Green"{1}"^N {2}', name, extrinsic(Name,o), _id(o))
    if len(t.__slots__) > 1:
        params = (repr(getattr(o, s)) for s in t.__slots__[:-1])
        comma = col('Blue', ', ')
        name = fmtcol('{0}^Blue(^N{1}^Blue)^N', name, comma.join(params))
    return name

Structured.__repr__ = __repr__

# Type annotations

def annot(t):
    def dec(func):
        func.typeannot = t
        return func
    return dec

# Matching

named_match_dispatch = {}

def match_try(atom, ast):
    if isinstance(ast, compiler.ast.CallFunc
                ) and isinstance(ast.node, compiler.ast.Name):
        if ast.node.name in CTORS:
            dt = CTORS[ast.node.name]
            if atom.__class__ != dt:
                return None
            slots = filter(lambda s: s != '_ix', dt.__slots__)
            assert len(ast.args) == len(slots), \
                    "Ctor %s takes %d args: %s" % (ast.node.name,
                            len(slots), ', '.join(slots))
            # Found a matching constructor; now match its args recursively
            # Unlike the main match loop, if any fail here everything fails
            ctor_args = []
            for (arg_ast, attrname) in zip(ast.args, slots):
                sub_args = match_try(getattr(atom, attrname), arg_ast)
                if sub_args is None:
                    return None
                ctor_args += sub_args
            return ctor_args
        named_matcher = named_match_dispatch.get(ast.node.name)
        if named_matcher is not None:
            return named_matcher(atom, ast)
        assert False, "Unknown match: %s (%s)" % (ast.node.name, ast.args)
    elif isinstance(ast, compiler.ast.Name):
        if ast.name == 'True':
            assert isinstance(atom, bool)
            return [] if atom else None
        elif ast.name == 'False':
            assert isinstance(atom, bool)
            return None if atom else []
        # Just a simple variable name match; always succeeds
        return [] if ast.name == '_' else [atom]
    elif isinstance(ast, compiler.ast.Const):
        # Literal match
        return [] if ast.value == atom else None
    elif isinstance(ast, (compiler.ast.Tuple, compiler.ast.List)):
        t = tuple if isinstance(ast, compiler.ast.Tuple) else list
        if not isinstance(atom, t) or len(atom) != len(ast.nodes):
            return None
        tuple_args = []
        for a, node in zip(atom, ast.nodes):
            args = match_try(a, node)
            if args is None:
                return None
            tuple_args += args
        return tuple_args
    elif isinstance(ast, compiler.ast.Or):
        # First that doesn't fail
        for case in ast.nodes:
            or_args = match_try(atom, case)
            if or_args is not None:
                return or_args
        return None
    elif isinstance(ast, compiler.ast.And):
        and_args = []
        for case in ast.nodes:
            case_args = match_try(atom, case)
            if case_args is None:
                return None
            and_args += case_args
        return and_args
    elif isinstance(ast, compiler.ast.Compare) and ast.ops[0][0] == '==':
        # capture right side
        assert isinstance(ast.expr, compiler.ast.Name) and ast.expr.name != '_'
        capture_args = match_try(atom, ast.ops[0][1])
        return [atom] + capture_args if capture_args is not None else None
    assert False, "Unknown match case: %s" % ast

match_asts = {}

def match(atom, *cases):
    # Block form
    if len(cases) == 0:
        return match_blocks(atom)
    elif len(cases) == 1 and isinstance(cases[0], basestring):
        # shortcut for single-case
        m = match_blocks(atom)
        if m(cases[0]):
            m.ret(m.arg if hasattr(m, 'arg') else m.args)
        return m.result()

    # Try all the cases, find the first that doesn't fail
    for (case, f) in cases:
        call_args = match_try(atom, _get_match_case(case))
        if call_args is not None:
            return f(*call_args)
    case_list = ''.join('* %s -> %s\n' % (p, f) for p, f in cases)
    assert False, "Match failed.\nVALUE:\n%r\nCASES:\n%s" % (atom, case_list)

def match_blocks(atom):
    cases = []
    def case(pat):
        cases.append(pat)
        args = match_try(atom, _get_match_case(pat))
        if args is None:
            return False
        if len(args) == 1:
            case.arg = args[0]
        else:
            case.args = args
        return True
    def ret(result):
        case.success = result
    case.ret = ret
    def result():
        if hasattr(case, 'success'):
            return case.success
        else:
            case_list = ''.join('* %s\n' % p for p in cases)
            assert False, "Match failed.\nVALUE:\n%r\nCASES:\n%s" % (atom,
                    case_list)
    case.result = result
    return case

def matches(atom, case):
    return match_try(atom, _get_match_case(case)) is not None

def _get_match_case(case):
    ast = match_asts.get(case)
    if ast is None:
        ast = compiler.parse(case, mode='eval').node
        match_asts[case] = ast
    return ast

# decorator
def matcher(name):
    def takes_func(func):
        named_match_dispatch[name] = func
        return func
    return takes_func

@matcher('contains')
def _match_contains(atom, ast):
    # Do any members of the list match?
    assert len(ast.args) == 1
    assert isinstance(atom, list), "Expected list for 'contains"
    for item in atom:
        item_args = match_try(item, ast.args[0])
        if item_args is not None:
            return item_args
    return None

@matcher('cons')
def _match_cons(atom, ast):
    # Matches args to (head, tail)
    assert len(ast.args) == 2
    assert isinstance(atom, list), "Expected list for 'cons"
    if len(atom):
        car = match_try(atom[0], ast.args[0])
        if car is not None:
            cdr = match_try(atom[1:], ast.args[1])
            if cdr is not None:
                return car + cdr
    return None

@matcher('all')
def _match_all(atom, ast):
    assert len(ast.args) == 2
    assert isinstance(ast.args[0], compiler.ast.Name)
    assert isinstance(atom, list)
    results = []
    all_singular = True
    for i in atom:
        r = match_try(i, ast.args[1])
        if r is not None:
            if len(r) != 1:
                all_singular = False
            results.append(r)
    if ast.args[0].name == '_':
        return []
    return [[r[0] for r in results] if all_singular else results]

@matcher('every')
def _match_every(atom, ast):
    assert len(ast.args) == 2
    assert isinstance(ast.args[0], compiler.ast.Name)
    assert isinstance(atom, list)
    results = []
    all_singular = True
    for i in atom:
        r = match_try(i, ast.args[1])
        if r is None:
            return None
        if len(r) != 1:
            all_singular = False
        results.append(r)
    if ast.args[0].name == '_':
        return []
    return [[r[0] for r in results] if all_singular else results]

Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'), 'Nothing')
def isJust(m): return matches(m, 'Just(_)')
def isNothing(m): return matches(m, 'Nothing()')
def maybe(no, yes, val):
    return match(val, ('Just(j)', yes), ('Nothing()', lambda: no))
def maybe_(no, val):
    return match(val, ('Just(j)', lambda j: j), ('Nothing()', lambda: no))
def fromJust(val):
    return match(val, ('Just(j)', lambda j: j))
def mapMaybe(f, val):
    return match(val, ('Just(j)', lambda j: Just(f(j))),
                      ('Nothing()', Nothing))

def hint(e, **kwargs):
    return e

# Will be replaced by bedrock.List equivalents

def cons(car, cdr):
    return [car] + cdr

def concat(lists):
    return reduce(list.__add__, lists, [])

def concat_map(f, xs):
    result = []
    for x in xs:
        result += f(x)
    return result

def map_(f, xs):
    for x in xs:
        f(x)

def unzip(list):
    first = []
    second = []
    for (f, s) in list:
        first.append(f)
        second.append(s)
    return (first, second)

def nop():
    pass

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
