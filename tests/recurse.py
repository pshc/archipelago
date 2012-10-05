from bedrock import *

@annot('int -> int')
def fact(a):
    if a < 1:
        return 1
    else:
        return a * fact(a-1)

def main():
    assert fact(10) == 3628800, "Factorial"
    return 0
