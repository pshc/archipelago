from bedrock import *

Account = DT('Account', ('balance', int))

def main():
    a = 1
    n = 0 
    while n < 10:
        a += a
        n = n + 1
    assert a == 1024, 'Power of two'

    account = Account(10)
    account.balance += 20
    assert account.balance == 30, 'Field augmentation'

    return 0
