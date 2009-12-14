def ok(n):
    s = n + 3
    print 's = %d' % (s,)
    return s
def ident(val):
    return val
def main():
    while False:
        inside = 1
    a = 1 + 2
    ok(a)
    if True:
        print 'ok'
    elif False:
        print 'what'
    else:
        print 'no'
    assert True, 'WHAT'
    t = (1, 2)
    c = None
    c = 'ok'
    Pair = DT('Pair', ('first', int), ('second', int))
    Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'), 'Nothing')
    m = Just(1)
    match(m, ("Just(n)", identity), ("Nothing()", lambda: 0))
    return 0

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
