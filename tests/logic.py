
@annot('void -> int')
def main():
    assert True or False, "Or"
    assert not (False or False), "Nor"
    assert True and True, "And"
    assert not (True and False), "Nand"
    assert False if 2+2 == 3 else True, "Ternary"
    return 0
