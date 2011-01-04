from base import DT, ADT, match

(List, Cons, Nil) = ADT('List', 'Cons', ('car', 'a'), ('cdr', 'List(a)'),
                                'Nil')

(Atom, Int, Str, Ref) = ADT('Atom',
                            'Int', ('intVal', int), ('subs', 'List(Atom)'),
                            'Str', ('strVal', str), ('subs', 'List(Atom)'),
                            'Ref', ('refAtom', 'Atom'), ('subs', 'List(Atom)'))

def str_(st):
    return Str(st, [])
def int_(n):
    return Int(n, [])
def ref_(a):
    return Ref(a, [])

Module = DT('Module', ('name', str), ('digest', str), ('roots', 'List(Atom)'))

Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'), 'Nothing')
def isJust(m): return match(m, ('Just(_)', lambda: True), ('_', lambda: False))
def isNothing(m): return match(m, ('Nothing()', lambda: True),
                                  ('_', lambda: False))
def maybe(no, yes, val):
    return match(val, ('Just(j)', yes), ('Nothing()', lambda: no))
def maybe_(no, val):
    return match(val, ('Just(j)', identity), ('Nothing()', lambda: no))
def fromJust(val):
    return match(val, ('Just(j)', identity))

def identity(val): return val
def tuple2(a, b): return (a, b)
def tuple3(a, b, c): return (a, b, c)
def tuple4(a, b, c, d): return (a, b, c, d)
def tuple5(a, b, c, d, e): return (a, b, c, d, e)

def fst(t):
    return match(t, ('(f, _)', identity))
def snd(t):
    return match(t, ('(_, s)', identity))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
