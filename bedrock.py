from base import DT, ADT, annot, match, new_extrinsic, hint

(List, Cons, Nil) = ADT('List', 'Cons', ('car', 'a'), ('cdr', 'List(a)'),
                                'Nil')

# TEMP
Set = DT('Set', ('contents', ['a']))
Dict = DT('Dict', ('contents', [('k', 'v')]))

Module = DT('Module', ('rootType', 'Type'), ('root', 'a'))
ModDigest = new_extrinsic('ModDigest', str)
ModDeps = new_extrinsic('ModDeps', '[*Module]')

@annot('a -> a')
def identity(val): return hint(val, a='a')

@annot('(a, b) -> (a, b)')
def tuple2(a, b): return (a, b)

@annot('(a, b, c) -> (a, b, c)')
def tuple3(a, b, c): return (a, b, c)

@annot('t(a, b) -> a')
def fst(t):
    return match(t, ('(f, _)', identity))

@annot('t(a, b) -> b')
def snd(t):
    return match(t, ('(_, s)', identity))

Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'), 'Nothing')
@annot('Maybe(a) -> bool')
def isJust(m):
    return match(m, ('Just(_)', lambda: True), ('_', lambda: False))
@annot('Maybe(a) -> bool')
def isNothing(m):
    return match(m, ('Nothing()', lambda: True), ('_', lambda: False))
@annot('(a, Maybe(a)) -> a')
def maybe_(no, val):
    return match(val, ('Just(j)', lambda j: j), ('Nothing()', lambda: no))
@annot('Maybe(a) -> a')
def fromJust(val):
    return match(val, ('Just(j)', lambda j: j))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
