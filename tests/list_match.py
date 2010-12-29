from bedrock import *

def main():
    a = [0, 1]
    a = [1, 2, 3]
    b = match(a, ("Cons(_, Cons(two, Cons(_, Nil())))", identity),
                 ("_", lambda: 4))
    assert b == 2, "List pattern match"
    return 0
