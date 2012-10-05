
def main():
    # ConstExpr tests
    assert 0 - 1 == -1, "Negative"
    assert 12 // 3 == 4, "Division"
    assert -13 // 3 == -4, "Signed floor division"
    assert 5 % 3 == 2, "Modulus"
    assert 12 & 24 == 8, "And"
    assert 1 | 2 == 3, "Or"
    assert 1 ^ 3 == 2, "Xor"
    assert 1 == 1, "Equal"
    assert 1 != 2, "Not equal"
    assert 1 < 2, "Less than"
    assert 2 > 1, "Greater than"

    # Instruction tests
    zero = 0
    one = 1
    two = 2
    three = 3
    four = 4
    assert zero - one == -one, "Negative"
    assert 12 // three == four, "Division"
    assert -13 // three == -four, "Signed floor division"
    assert 5 % three == two, "Modulus"
    assert 12 & 24 == two*four, "And"
    assert one | two == three, "Or"
    assert one ^ three == two, "Xor"
    assert one == one, "Equal"
    assert one != two, "Not equal"
    assert one < two, "Less than"
    assert two > one, "Greater than"
    return 0
