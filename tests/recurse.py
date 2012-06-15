from bedrock import *

@annot('int -> int')
def fact(a):
    if a < 1:
        return 1
    else:
        return a * fact(a-1)

@annot('void -> int')
def main():
    # workaround while we don't have support for big ints
    assert fact(10) == 90 * 4032, "Factorial"
    return 0
