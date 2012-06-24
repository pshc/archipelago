
@annot('void -> int')
def main():
    assert 0 - 1 == -1, "Negative"
    assert 12 // 3 == 4, "Division"
    assert -13 // 3 == -4, "Signed floor division"
    assert 5 % 3 == 2, "Modulus"
    assert 12 & 24 == 8, "And"
    assert 1 | 2 == 3, "Or"
    assert 1 ^ 3 == 2, "Or"
    return 0
