
@annot('void -> bool')
def should_be_skipped():
    assert False, "Short-circuit"
    return False

def main():
    assert True or True, "Or"
    assert True or False, "Or"
    assert False or True, "Or"
    assert not (False or False), "Nor"
    assert True or should_be_skipped(), "Or short-circuit"

    assert True and True, "And"
    assert not (True and False), "Nand"
    assert not (False and True), "Nand"
    assert not (False and False), "Nand"
    assert not (False and should_be_skipped()), "And short-circuit"

    assert False if 2+2 == 3 else True, "Ternary"
    return 0
