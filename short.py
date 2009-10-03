def ok(n):
    n = n + 3
    print 'n = %d' % (n,)
    return n
def ident(val):
    return val
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
Pair = DT('Pair', ('first', None), ('second', None))

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
