import compiler
from types import FunctionType

DATATYPES = {}
ALGETYPES = {}

_deferred_type_parses = []

def DT(*members, **opts):
    members = list(members)
    superclass = opts.get('superclass', DataType)
    name = members.pop(0)
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
  def __init__(self%(args)s):
    self._ix = %(ix)d
%(stmts)s""" % locals()
    exec code
    dt = DATATYPES[name] = eval(name)
    dt.ctors = [dt]
    for nm, t in members:
        if _deferred_type_parses is None:
            t = parse_type(t)
        dt.__types__.append(t)
    if invariant:
        dt.check_invariant = invariant
    if _deferred_type_parses is not None:
        _deferred_type_parses.append(dt)
    return dt

def ADT(*ctors):
    ctors = list(ctors)
    tname = ctors.pop(0)
    exec 'class %s(DataType): ctors = []' % (tname,)
    t = eval(tname)
    data = [t]
    ALGETYPES[tname] = t
    ctor_ix = 0
    while ctors:
        ctor = ctors.pop(0)
        members = []
        while ctors and not isinstance(ctors[0], basestring):
            members.append(ctors.pop(0))
        d = DT(ctor, *members, **dict(superclass=t))
        d.__module__ = tname
        d._ctor_ix = ctor_ix
        ctor_ix += 1
        t.ctors.append(d)
        data.append(d)
    return tuple(data)

class DataType(object):
    pass

# Type representations

TypeVar = DT('TypeVar')

Type, TVar, TMeta, TInt, TStr, TChar, TBool, TVoid, \
    TTuple, TAnyTuple, TFunc, TData, TApply, TWeak \
    = ADT('Type',
        'TVar', ('typeVar', '*TypeVar'),
        'TMeta', ('metaType', 'Maybe(Type)'),
        'TInt', 'TStr', 'TChar', 'TBool',
        'TVoid',
        'TTuple', ('tupleTypes', ['Type']),
        'TAnyTuple',
        'TFunc', ('funcArgs', ['Type']), ('funcRet', 'Type'),
        'TData', ('data', '*DTStmt'),
        'TApply', ('appType', 'Type'), ('appVars', ['Type']),
        'TWeak', ('refType', 'Type'))

_parsed_type_cache = {}

def parse_type(t):
    if type(t) is type and issubclass(t, DataType):
        return TData(t)
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
    elif isinstance(t, tuple):
        return TTuple(map(parse_type, t))
    elif isinstance(t, list):
        assert len(t) == 1
        return _apply_list_type(parse_type(t[0]))
    elif isinstance(t, set):
        assert len(t) == 1
        return _apply_set_type(parse_type(list(t)[0]))
    elif isinstance(t, dict):
        assert len(t) == 1
        [(key, val)] = t.iteritems()
        return _apply_dict_type(parse_type(key), parse_type(val))
    elif t is None or t is type or t is object or t is file:
        # MAGIC!
        return t
    assert False, "Unknown type repr of type %r: %r" % (type(t), t)

def realize_type(t):
    ast = compiler.ast
    if isinstance(t, ast.CallFunc):
        return TApply(realize_type(t.node), map(realize_type, t.args))
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
        return reduce(lambda r, ts: TFunc(map(realize_type, ts), r), ops, r)
    elif isinstance(t, ast.List):
        assert len(t.nodes) == 1
        return _apply_list_type([realize_type(t.nodes[0])])
    elif isinstance(t, ast.Tuple):
        return TTuple(map(realize_type, t.nodes))
    elif isinstance(t, ast.Name):
        t = t.name
        if len(t) == 1:
            return TVar(t)
        elif t in ALGETYPES:
            return TData(ALGETYPES[t])
        elif t in DATATYPES:
            return TData(DATATYPES[t])
        elif t == 'str':
            return TStr()
        elif t == 'int':
            return TInt()
        else:
            return TForward(t)
    elif isinstance(t, ast.UnarySub):
        return TWeak(realize_type(t.expr))
    assert False, "Unknown type ast repr: %r" % (t,)

TForward = DT('TForward', ('name', str))

def _apply_list_type(t):
    return TApply(list, [t])

def _apply_set_type(t):
    return TApply(set, [t])

def _apply_dict_type(k, v):
    return TApply(dict, [k, v])

# Parse the types in TypeVar, Type fields
def _parse_deferred():
    global _deferred_type_parses
    for ctor in _deferred_type_parses:
        ctor.__types__ = map(parse_type, ctor.__types__)
    _deferred_type_parses = None
_parse_deferred()

# Contexts

ContextInfo = DT('ContextInfo', ('ctxtName', str), ('ctxtType', type),
                                ('ctxtStack', '[a]'))

def new_context(name, t):
    assert isinstance(name, basestring)
    assert isinstance(t, type)
    return ContextInfo(name, t, [])

def in_context(ctxt, initial, func):
    assert isinstance(initial, ctxt.ctxtType)
    stack = ctxt.ctxtStack
    stack.append(initial)
    count = len(stack)
    ret = func()
    assert len(stack) == count, 'Imbalanced context %s stack' % ctxt.ctxtName
    stack.pop()
    return ret

def context(ctxt):
    assert len(ctxt.ctxtStack), 'Not in context %s at present' % ctxt.ctxtName
    return ctxt.ctxtStack[-1]

# Extrinsics

ExtInfo = DT('ExtInfo', ('label', str), ('t', type), ('stack', [{'a': 't'}]))

def new_extrinsic(label, t):
    stack = []
    # XXX: Omnipresent for now
    if label == 'Name':
        stack = [{}]
    return ExtInfo(label, t, stack)

def extrinsic(ext, obj):
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

def in_extrinsic_scope(ext):
    return bool(ext.stack)

def add_extrinsic(ext, obj, val):
    assert not isinstance(obj, value_types), "No extrinsics on values"
    assert ext.stack, "Not in extrinsic %s" % (ext.label,)
    map = ext.stack[-1]
    assert obj not in map, "%r already has %s extrinsic" % (obj, ext.label)
    map[obj] = val

def update_extrinsic(ext, obj, val):
    assert not isinstance(obj, value_types), "No extrinsics on values"
    map = ext.stack[-1]
    assert obj in map, "%r doesn't have %s extrinsic yet" % (obj, ext.label)
    map[obj] = val

def has_extrinsic(ext, obj):
    assert not isinstance(obj, value_types), "No extrinsics on values"
    return obj in ext.stack[-1]

value_types = (basestring, bool, int, float, tuple, type(None))

# Pretty printing
# (naive quadratic version)

PrettyPrinted = new_extrinsic('PrettyPrinted', type(None))

def pretty_brief(name, o):
    if name == 'BindBuiltin':
        from bedrock import Name
        return '&%s' % extrinsic(Name, o.builtin)
    elif name == 'IntLit':
        return 'i%d' % (o.val,)
    elif name == 'StrLit':
        return 's%r' % (o.val,)
    elif name == 'TupleLit':
        return 't%r' % (tuple(o.vals),)
    return None

def __repr__(o):
    from bedrock import Name
    if not in_extrinsic_scope(PrettyPrinted):
        return scope_extrinsic(PrettyPrinted, lambda: repr(o))
    t = type(o)
    name = t.__name__
    if has_extrinsic(PrettyPrinted, o):
        if has_extrinsic(Name, o):
            name = '%s "%s"' % (name, extrinsic(Name, o))
        return '<%s at 0x%x>' % (name, id(o))
    add_extrinsic(PrettyPrinted, o, None)

    brief = pretty_brief(name, o)
    if brief is not None:
        return brief

    if has_extrinsic(Name, o):
        name = '%s "%s"' % (name, extrinsic(Name, o))
    params = (repr(getattr(o, s)) for s in t.__slots__[:-1])
    return '%s(%s)' % (name, ', '.join(params))

DataType.__repr__ = __repr__

# Matching

named_match_dispatch = {}

def match_try(atom, ast):
    if isinstance(ast, compiler.ast.CallFunc
                ) and isinstance(ast.node, compiler.ast.Name):
        if ast.node.name in DATATYPES:
            dt = DATATYPES[ast.node.name]
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
    elif isinstance(ast, compiler.ast.Name):
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
    # Try all the cases, find the first that doesn't fail
    for (case, f) in cases:
        ast = match_asts.get(case)
        if ast is None:
            ast = compiler.parse(case, mode='eval').node
            match_asts[case] = ast
        call_args = match_try(atom, ast)
        if call_args is not None:
            return f(*call_args)
    case_list = ''.join('* %s -> %s\n' % (p, f) for p, f in cases)
    assert False, "Match failed.\nVALUE:\n%s\nCASES:\n%s" % (atom, case_list)

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

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
