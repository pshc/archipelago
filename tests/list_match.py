from bedrock import *

@annot('void -> int')
def main():
    a = hint(Cons(0, Cons(1, Nil())), a='int')
    a = hint(Cons(1, Cons(2, Cons(3, Nil))), a='int')
    #b = hint(match(a, ("Cons(_, Cons(two, Cons(_, Nil())))", identity),
    #             ("_", lambda: 4)), a='int')
    #assert b == 2, "List pattern match"
    return 0
