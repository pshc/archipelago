from base import DT, ADT, annot, cdecl, hint, match, new_extrinsic

(List, Cons, Nil) = ADT('List', 'Cons', ('car', 'a'), ('cdr', 'List(a)'),
                                'Nil')

# TEMP
Set = DT('Set', ('contents', ['a']))
Dict = DT('Dict', ('contents', [('k', 'v')]))

Module = DT('Module', ('rootType', 'Type'), ('root', 'a'))
ModDigest = new_extrinsic('ModDigest', str)
ModDeps = new_extrinsic('ModDeps', '[*Module]')

@annot('a -> a', env=False)
def identity(val): return val

@annot('(a, b) -> (a, b)', env=False)
def tuple2(a, b): return (a, b)

@annot('(a, b, c) -> (a, b, c)', env=False)
def tuple3(a, b, c): return (a, b, c)

@annot('t(a, b) -> a', env=False)
def fst(t):
    return match(t, ('(f, _)', identity))

@annot('t(a, b) -> b', env=False)
def snd(t):
    return match(t, ('(_, s)', identity))

Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'),
                                    'Nothing',
                                    value=True)
@annot('Maybe(a) -> bool', env=False)
def isJust(m):
    return match(m, ('Just(_)', lambda: True), ('_', lambda: False))

@annot('Maybe(a) -> bool', env=False)
def isNothing(m):
    return match(m, ('Nothing()', lambda: True), ('_', lambda: False))

@annot('(a, Maybe(a)) -> a', env=False)
def maybe_(no, val):
    return match(val, ('Just(j)', lambda j: j), ('Nothing()', lambda: no))

@annot('Maybe(a) -> a', env=False)
def fromJust(val):
    return match(val, ('Just(j)', lambda j: j))

puts = cdecl('puts', 'str -> void')

# TEMP
_print_str = cdecl('_print_str', 'str -> void')
_print_int = cdecl('_print_int', 'int -> void')
_newline = cdecl('_newline', 'void -> void')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
