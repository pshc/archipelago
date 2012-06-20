from bedrock import *

@annot('int -> int')
def fact(a):
    if a < 1:
        return 1
    else:
        return a * fact(a-1)

@annot('void -> int')
def main():
    assert fact(10) == 322560, "Factorial"
    return 0
