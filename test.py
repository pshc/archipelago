from base import DT, ADT

Pair = DT('Pair', ('first', 'a'), ('second', 'b'))

a = 10
buf = ""
while a > 4:
    a = a - 1
    buf = "%s%d" % (buf, a)
assert buf == "987654" and a == 4
def foo(bar, baz):
    print "%s" % (baz,)
    return bar + bar
assert foo(42, "OK") == 84
greeting = [(True, "ello"), (True, "friend")]
greeting[1] = (False, "world")
buf = ""
for b, c in greeting:
    if b:
        buf = "%sh" % (buf,)
    buf = "%s%s" % (buf, c)
    while True:
        break
    continue
    print "continue FAIL"
assert buf == "helloworld"
p = Pair(1, 2)
assert p.first == 1 and p.second == 2
p.first = 4
assert p.first == 4 and p.second == 2

n, j = Nothing(), Just("OK")
print "%s" % (match(n, ("Just(msg)", lambda m: m),
                       ("Nothing()", lambda: "OK")),)
print "%s" % (match(j, ("Just(msg)", lambda m: m),
                       ("Nothing()", lambda: "match FAIL")),)

def fac(n):
    if n == 0:
        return 1
    return n * fac(n - 1)
assert fac(5) == 120

ns = [0, 2, 0, 0, 1]
print "%s" % (match(ns, ("every(_, 0)",  lambda: "every(...) FAILED"),
                        ("_",            lambda: "OK")),)
print "%s" % (match(ns, ("all(_, l==0)", lambda: "OK"),
                        ("_",            lambda: "all(...) FAILED")),)

def one(k): return two(k)
def two(k): return k + k
assert one(10) == 20
# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
