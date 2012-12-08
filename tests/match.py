
Cell = DT('Cell', ('vitality', int))

def main():
    assert match(Cell(50), ("Cell(n)", lambda n: n + 1)) == 51, "Match"

    m = match(Cell(20))
    if m('Cell(21)'):
        assert False, "Wrong block intlit match"
    elif m('Cell(x)'):
        assert m.x == 20, "Block intlit binding"

    return 0
