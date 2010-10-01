from base import ADT

(Atom, Int, Str, Ref) = ADT('Atom',
                            'Int', ('intVal', int), ('subs', ['Atom']),
                            'Str', ('strVal', str), ('subs', ['Atom']),
                            'Ref', ('refAtom', 'Atom'), ('refMod', 'Module'),
                                   ('subs', ['Atom']))

Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'), 'Nothing')
def isJust(m): return match(m, ('Just(_)', lambda: True), ('_', lambda: False))
def isNothing(m): return match(m, ('Nothing()', lambda: True),
                                  ('_', lambda: False))

def str_(st):
    return Str(st, [])
def int_(n):
    return Int(n, [])

def identity(val): return val
def tuple2(a, b): return (a, b)
def tuple3(a, b, c): return (a, b, c)
def tuple4(a, b, c, d): return (a, b, c, d)
def tuple5(a, b, c, d, e): return (a, b, c, d, e)

def fst(t):
    (f, s) = t
    return f
def snd(t):
    (f, s) = t
    return s

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
