import compiler
from compiler.ast import *

datatypes = {}
algetypes = {}

def DT(*members):
    name = members[0]
    mems = [(nm) for (nm, t) in members[1:]]
    code = """class %s(object):
  __slots__ = [%s]
  def __init__(self, %s):
%s""" % (name, ', '.join(map(repr, mems)), ', '.join(mems),
        ''.join(['    self.%s = %s\n' % (m, m) for m in mems]))
    exec code
    dt = datatypes[name] = eval(name)
    return dt

def ADT(*ctors):
    ctors = list(ctors)
    tname = ctors.pop(0)
    exec 'class %s(object): ctors = []' % (tname,)
    data = [eval(tname)]
    algetypes[tname] = data[0]
    while ctors:
        ctor = ctors.pop(0)
        members = []
        while ctors and isinstance(ctors[0], tuple):
            members.append(ctors.pop(0))
        d = DT(ctor, *members)
        data[0].ctors.append(d)
        data.append(d)
    return tuple(data)

named_match_dispatch = {}

def match_try(atom, ast):
    if isinstance(ast, CallFunc) and isinstance(ast.node, Name):
        if ast.node.name in datatypes:
            dt = datatypes[ast.node.name]
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
    assert False, "Unknown match case: %s" % ast

def match(atom, *cases):
    # Try all the cases, find the first that doesn't fail
    for (case, f) in cases:
        ast = compiler.parse(case, mode='eval').node
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
def match_contains(atom, ast):
    # Do any members of the list match?
    assert len(ast.args) == 1
    assert isinstance(atom, list), "Expected list for 'contains"
    for item in atom:
        item_args = match_try(item, ast.args[0])
        if item_args is not None:
            return item_args
    return None

@matcher('cons')
def match_cons(atom, ast):
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
def match_all(atom, ast):
    assert len(ast.args) == 1
    assert isinstance(atom, list)
    return [filter(lambda r: r is not None,
                   [match_try(i, ast.args[0]) for i in atom])]

def const(val):
    return lambda x: val

def identity(val):
    return val

def maybe(default, func, expr):
    return default if expr is None else func(expr)

# Avoid tuples in args for simplicity
def fst(t):
    (f, s) = t
    return f
def snd(t):
    (f, s) = t
    return s

def concat(lists):
    return reduce(list.__add__, lists, [])

def unzip(list):
    first = []
    second = []
    for (f, s) in list:
        first.append(f)
        second.append(s)
    return (first, second)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
