from base import DT, ADT

Pair = DT('Pair', ('first', None), ('second', None))
Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', None), 'Nothing')

def foo(bar, baz):
    print baz
    return bar + bar
a = 10
while a > 4:
    print a
    a = a - 1
greeting = [(True, "ello"), (True, "friend")]
greeting[1] = (False, "world")
for b, c in greeting:
    if b:
        print 'h'
    print c
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
p.first = 4
print p.first
print p.second

n, j = Nothing(), Just("just value")
print match(n, ("Just(msg)", lambda m: m), ("Nothing()", lambda: "nothing"))
print match(j, ("Just(msg)", lambda m: m), ("Nothing()", lambda: "nothing"))

def fac(n):
    if n == 0:
        return 1
    return n * fac(n - 1)

print fac(5)
