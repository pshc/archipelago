from bedrock import *

def main():
    a = Cons(0, Cons(1, Nil()))
    a = Cons(1, Cons(2, Cons(3, Nil)))
    b = match(a, ("Cons(_, Cons(two, Cons(_, Nil())))", identity),
                 ("_", lambda: 4))
    assert b == 2, "List pattern match"
    return 0
