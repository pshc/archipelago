import compiler
from compiler.ast import *

DATATYPES = {}
ALGETYPES = {}

def DT(*members):
    name = members[0]
    mems = [(nm) for (nm, t) in members[1:]]
    slots = ', '.join(map(repr, mems) + ['"_ix"'])
    args = ''.join(', %s' % m for m in mems)
    ix = len(DATATYPES)
    stmts = ''.join(['    self.%s = %s\n' % (m, m) for m in mems])
    code = """class %(name)s(object):
  __slots__ = [%(slots)s]
  def __init__(self%(args)s):
    self._ix = %(ix)d
%(stmts)s""" % locals()
    exec code
    dt = DATATYPES[name] = eval(name)
    return dt

def ADT(*ctors):
    ctors = list(ctors)
    tname = ctors.pop(0)
    exec 'class %s(object): ctors = []' % (tname,)
    data = [eval(tname)]
    ALGETYPES[tname] = data[0]
    while ctors:
        ctor = ctors.pop(0)
        members = []
        while ctors and isinstance(ctors[0], tuple):
            members.append(ctors.pop(0))
        d = DT(ctor, *members)
        data[0].ctors.append(d)
        data.append(d)
    return tuple(data)

Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'), 'Nothing')

named_match_dispatch = {}

def match_try(atom, ast):
    if isinstance(ast, CallFunc) and isinstance(ast.node, Name):
        if ast.node.name in DATATYPES:
            dt = DATATYPES[ast.node.name]
            if atom.__class__ != dt:
                return None
            # Found a matching constructor; now match its args recursively
            # Unlike the main match loop, if any fail here everything fails
            ctor_args = []
            for (arg_ast, attrname) in zip(ast.args, dt.__slots__):
                sub_args = match_try(getattr(atom, attrname), arg_ast)
                if sub_args is None:
                    return None
                ctor_args += sub_args
            return ctor_args
        named_matcher = named_match_dispatch.get(ast.node.name)
        if named_matcher is not None:
            return named_matcher(atom, ast)
    elif isinstance(ast, Name):
        # Just a simple variable name match; always succeeds
        return [] if ast.name == '_' else [atom]
    elif isinstance(ast, Const):
        # Literal match
        return [] if ast.value == atom else None
    elif isinstance(ast, Tuple):
        if not isinstance(atom, tuple) or len(atom) != len(ast.nodes):
            return None
        tuple_args = []
        for a, node in zip(atom, ast.nodes):
            args = match_try(a, node)
            if args is None:
                return None
            tuple_args += args
        return tuple_args
    elif isinstance(ast, Or):
        # First that doesn't fail
        for case in ast.nodes:
            or_args = match_try(atom, case)
            if or_args is not None:
                return or_args
        return None
    elif isinstance(ast, And):
        and_args = []
        for case in ast.nodes:
            case_args = match_try(atom, case)
            if case_args is None:
                return None
            and_args += case_args
        return and_args
    elif isinstance(ast, Compare) and ast.ops[0][0] == '==':
        # capture right side
        assert isinstance(ast.expr, Name) and ast.expr.name != '_'
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
    assert isinstance(ast.args[0], Name)
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
    assert isinstance(ast.args[0], Name)
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


def identity(val):
    return val

# Avoid tuples in args for simplicity
def fst(t):
    (f, s) = t
    return f
def snd(t):
    (f, s) = t
    return s

def concat(lists):
    return reduce(list.__add__, lists, [])

def concat_map(f, xs):
    result = []
    for x in xs:
        result += f(xs)
    return result

def unzip(list):
    first = []
    second = []
    for (f, s) in list:
        first.append(f)
        second.append(s)
    return (first, second)

def tuple2(a, b): return (a, b)
def tuple3(a, b, c): return (a, b, c)
def tuple4(a, b, c, d): return (a, b, c, d)
def tuple5(a, b, c, d, e): return (a, b, c, d, e)


# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
