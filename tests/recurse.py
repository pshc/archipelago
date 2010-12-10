from bedrock import *

def fact(a):
    if a < 1:
        return 1
    else:
        return a * fact(a-1)

def main():
    print "fact(10) = %d" % (fact(10),)
    return 0
