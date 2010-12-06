import stdlib

def ok(n):
    s = n + 3
    print 's = %d' % (s,)
    return s
def ident(val):
    return val
ident2 = lambda v: v
Pair = DT('Pair', ('first', 'a'), ('second', 'b'))
def swap(pair):
    return match(pair, ("Pair(f, s)", lambda f, s: Pair(s, f)))
def main():
    while False:
        inside = 1
    id = ident
    a = id(1 + 2)
    id2 = ident2
    b = id2('nope.avi')
    ok(a)
    if True == True:
        print 'ok'
    elif False:
        print 'what'
    else:
        print 'no'
    assert True, 'WHAT'
    c = None
    c = 'ok'
    m = Just(1)
    match(m, ("Just(n)", id2), ("Nothing()", lambda: 0))
    p = Pair(1, ('hello', 'world'))
    print "%s %s" % (match(p,
        ("p==Pair(1, ('baby', 'universe'))", lambda p: "wrong"),
        ("Pair(_, (msg, 'world'))", identity)), p.second)
    return 0

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
