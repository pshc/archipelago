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
p.first = 4
print p.first
print p.second

n = Nothing()
j = Just("just value")
print j.just
