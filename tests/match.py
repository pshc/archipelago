
Cell = DT('Cell', ('vitality', int))

def main():
    assert match(Cell(50), ("Cell(n)", lambda n: n + 1)) == 51, "Match"
    return 0
