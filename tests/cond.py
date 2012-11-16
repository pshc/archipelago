Wumpus = DT('Wumpus')

@annot('int -> int')
def test(n):
    res = 0
    w = Wumpus()
    if n == 0:
        w2 = Wumpus()
        res = 1
    elif n == 1:
        res = 2
    elif n == 2:
        w3 = Wumpus()
        return 4
    else:
        res = test(n-2) * 4
    return res

def main():
    assert test(8) == 256
    return 0
