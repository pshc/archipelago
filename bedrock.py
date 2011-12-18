from base import DT, ADT, match, new_extrinsic

(List, Cons, Nil) = ADT('List', 'Cons', ('car', 'a'), ('cdr', 'List(a)'),
                                'Nil')

# TEMP
Set = DT('Set', ('contents', ['a']))
Dict = DT('Dict', ('contents', [('k', 'v')]))

Module = DT('Module', ('rootType', 'Type'), ('root', 'a'))
ModDigest = new_extrinsic('ModDigest', str)

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
