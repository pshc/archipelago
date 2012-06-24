
@annot('void -> int')
def main():
    assert 0 - 1 == -1, "Negative"
    assert 12 // 3 == 4, "Division"
    assert -13 // 3 == -4, "Signed floor division"
    assert 5 % 3 == 2, "Modulus"
    return 0
