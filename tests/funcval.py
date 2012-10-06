
@annot('int -> int')
def triple(n):
    return n * 3

@annot('(int -> int) -> int')
def apply_two(f):
    g = f
    return g(2)

def main():
    assert apply_two(triple) == 6, "Function object"
    return 0
