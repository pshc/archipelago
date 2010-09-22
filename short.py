#def ok(n):
#    s = n + 3
#    print 's = %d' % (s,)
#    return s
def ident(val):
    return val
#Pair = DT('Pair', ('first', 'a'), ('second', 'b'))
#Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'), 'Nothing')
#Pair = DT('Pair', ('first', 'a'), ('second', 'b'))
Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', int), 'Nothing')
def main():
    while False:
        inside = 1
    a = ident(1 + 2)
    #ok(a)
    if True:
        print 'ok'
    elif False:
        print 'what'
    else:
        print 'no'
    assert True, 'WHAT'
    #t = (1, 2)
    #c = None
    c = 'ok'
    m = Just(1)
    #id2 = ident
    #match(m, ("Just(n)", id2), ("Nothing()", lambda: 0))
    #p = Pair(1, ('hello', 'world'))
    #print "%s %s" % (match(p,
    #    ("p==Pair(1, ('baby', 'universe'))", lambda p: "wrong"),
    #    ("Pair(_, (msg, 'world'))", identity)), p.second)
    return 0

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
