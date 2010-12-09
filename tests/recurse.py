def fib(a):
    if a <= 1:
        return 1
    else:
        return a * fib(a-1)

def main():
    print "fib(10) = %d\n" % (fib(10),)
    return 0
