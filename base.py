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

def match_try(atom, ast):
    if isinstance(ast, CallFunc) and isinstance(ast.node, Name) \
                                 and ast.node.name in datatypes:
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
    elif isinstance(ast, Name):
        # Just a simple variable name match; always succeeds
        return [] if ast.name == '_' else [atom]
    elif isinstance(ast, Const):
        # Literal match
        return [] if ast.value == atom else None
    assert False, "Unknown match case: %s" % ast

def match(atom, *cases):
    # Try all the cases, find the first that doesn't fail
    for (case, f) in cases:
        ast = compiler.parse(case, mode='eval').node
        call_args = match_try(atom, ast)
        if call_args is not None:
            return f(*call_args)
    assert False, "Match failed: %s %s" % (atom, cases)

def const(val):
    return lambda x: val

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
