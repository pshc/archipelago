from bedrock import *

def main():
    a = [1, 2, 3]
    b = match(a, ("Cons(_, Cons(two, _))", identity))
    print "Second: %d\n" % (b,)
    return 0
