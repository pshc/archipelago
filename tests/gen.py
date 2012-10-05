
@annot('a -> int')
def const(x):
    return 1

def main():
    assert const("Hi") == 1, "Generalization"
    assert const(5) == 1, "Generalization"
    return 0
