from bedrock import *

def main():
    a = 1
    n = 0 
    while n < 10:
        a += a
        n = n + 1
    assert a == 1024, 'Power of two'
    return 0
