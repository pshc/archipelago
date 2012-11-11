from bedrock import *

@annot('int -> int')
def hairy(i):
    n = 0
    while i > 0:
        n = n + 1
        if i > 10:
            if i == 199:
                break
            if i > 100:
                j = 3
                while True:
                    if j < 1:
                        break
                    i = i - 10
                    j = j - 1
            i = i - 3
            if i < 21:
                continue
            i = i - 1
        elif i < 5:
            i = i - 1
        else:
            i = i - 2
    return n

def main():
    assert hairy(-1) == 0
    assert hairy(2) == 2
    assert hairy(3) == 3
    assert hairy(5) == 4
    assert hairy(6) == 5
    assert hairy(9) == 6
    assert hairy(12) == 7
    assert hairy(15) == 8
    assert hairy(16) == 9
    assert hairy(21) == 10
    assert hairy(22) == 11
    assert hairy(25) == 11
    assert hairy(26) == 12
    assert hairy(80) == 25
    assert hairy(100) == 30
    assert hairy(101) == 23
    assert hairy(199) == 1
    assert hairy(200) == 33
    return 0
