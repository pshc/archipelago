@annot('int -> int')
def test(n):
    res = 0
    if n == 0:
        res = 1
    elif n == 1:
        res = 2
    elif n == 2:
        return 4
    else:
        res = test(n-2) * 4
    return res

@annot('void -> int')
def main():
    assert test(8) == 256
    return 0
