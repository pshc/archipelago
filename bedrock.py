from base import DT, ADT, annot, match, new_extrinsic, hint

(List, Cons, Nil) = ADT('List', 'Cons', ('car', 'a'), ('cdr', 'List(a)'),
                                'Nil')

# TEMP
Set = DT('Set', ('contents', ['a']))
Dict = DT('Dict', ('contents', [('k', 'v')]))

Module = DT('Module', ('rootType', 'Type'), ('root', 'a'))
ModDigest = new_extrinsic('ModDigest', str)

@annot('a -> a')
def identity(val): return hint(val, a='a')

@annot('(a, b) -> (a, b)')
def tuple2(a, b): return (a, b)

@annot('t(a, b) -> a')
def fst(t):
    return match(t, ('(f, _)', lambda f: f))

@annot('t(a, b) -> b')
def snd(t):
    return match(t, ('(_, s)', lambda s: s))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
