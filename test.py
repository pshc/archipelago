Pair = DT('Pair', ('first', None), ('second', None))

def foo(bar, baz):
    print baz
    return bar + bar
a = 10
while a > 4:
    print a
    a = a - 1
greeting = ["hello", "there"]
greeting[1] = "world"
for b in greeting:
    print b
    while 0:
        break
    continue
    print "!!!"
if a == 5:
    print 'INCORRECT'
elif a == 4:
    print foo(a, 'YES')
    print a
else:
    print 'NO'
p = Pair(1, 2)
print p.first
print p.second
