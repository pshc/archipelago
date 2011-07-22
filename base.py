import compiler
from types import FunctionType

DATATYPES = {}
ALGETYPES = {}

def DT(*members, **opts):
    members = list(members)
    superclass = opts.get('superclass', object)
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
    for nm, t in members:
        dt.__types__.append(t)
    if invariant:
        dt.check_invariant = invariant
    return dt

def ADT(*ctors):
    ctors = list(ctors)
    tname = ctors.pop(0)
    exec 'class %s(object): ctors = []' % (tname,)
    t = eval(tname)
    data = [t]
    ALGETYPES[tname] = t
    while ctors:
        ctor = ctors.pop(0)
        members = []
        while ctors and not isinstance(ctors[0], basestring):
            members.append(ctors.pop(0))
        d = DT(ctor, *members, **dict(superclass=t))
        d.__module__ = tname
        t.ctors.append(d)
        data.append(d)
    return tuple(data)

# Contexts

ContextInfo = DT('ContextInfo', ('ctxtName', str), ('ctxtType', 'type'),
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
    return ExtInfo(label, t, [])

def extrinsic(ext, obj):
    return ext.stack[-1][obj]

def scope_extrinsic(ext, func):
    new = ext.stack[-1].copy() if len(ext.stack) else {}
    ext.stack.append(new)
    ret = func()
    n = ext.stack.pop()
    assert n is new, "Extrinsic stack imbalance"
    return ret

def add_extrinsic(ext, obj, val):
    map = ext.stack[-1]
    assert obj not in map
    map[obj] = val

def update_extrinsic(ext, obj, val):
    map = ext.stack[-1]
    assert obj in map
    map[obj] = val

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
    elif isinstance(ast, compiler.ast.Tuple):
        if not isinstance(atom, tuple) or len(atom) != len(ast.nodes):
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
    assert False, "Match failed: %s %s" % (atom, cases)

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
