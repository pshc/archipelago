
@annot('int -> int')
def triple(n):
    return n * 3

@annot('(int -> int) -> int')
def apply_two(f):
    g = f
    return g(2)

@annot('void -> void')
def make_multiple_func_vals():
    # Sanity check ctx bindings
    # XXX: test actual env operations, not just compilation success
    f1 = triple
    f2 = triple
    assert f1(1) + f2(2) == 9, "Ctx-bound func vals"

def main():
    assert apply_two(triple) == 6, "Function object"
    make_multiple_func_vals()
    return 0
