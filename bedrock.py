from base import DT, ADT, annot, cdecl, hint, match, new_extrinsic
from maybe import *

(List, Cons, Nil) = ADT('List', 'Cons', ('car', 'a'), ('cdr', 'List(a)'),
                                'Nil')

# XXX antiquated
Set = DT('Set', ('contents', ['a']))
Dict = DT('Dict', ('contents', [('k', 'v')]))

ModDigest = new_extrinsic('ModDigest', str)
ModDeps = new_extrinsic('ModDeps', '[*Module]')

@annot('a -> a noenv')
def identity(val): return val

@annot('(a, b) -> (a, b) noenv')
def tuple2(a, b): return (a, b)

@annot('(a, b, c) -> (a, b, c) noenv')
def tuple3(a, b, c): return (a, b, c)

@annot('t(a, b) -> a noenv')
def fst(t):
    return match(t, ('(f, _)', identity))

@annot('t(a, b) -> b noenv')
def snd(t):
    return match(t, ('(_, s)', identity))

@annot('Maybe(a) -> bool noenv')
def isJust(m):
    return match(m, ('Just(_)', lambda: True), ('_', lambda: False))

@annot('Maybe(a) -> bool noenv')
def isNothing(m):
    return match(m, ('Nothing()', lambda: True), ('_', lambda: False))

@annot('(a, Maybe(a)) -> a noenv')
def maybe_(no, val):
    return match(val, ('Just(j)', lambda j: j), ('Nothing()', lambda: no))

@annot('Maybe(a) -> a noenv')
def fromJust(val):
    return match(val, ('Just(j)', lambda j: j))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
