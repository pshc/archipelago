
@annot('int -> int noenv')
def triple(n):
    return n * 3

@annot('(int -> int noenv) -> int noenv')
def apply_two(f):
    g = f
    return g(2)

FV = new_env('FV', int)

@annot('void -> int')
def getctx():
    return env(FV)

@annot('void -> void')
def make_multiple_func_vals():
    # Sanity check multiple FuncVal ctx bindings
    f1 = getctx
    f2 = getctx
    assert f1() + f2() == 8, "Ctx-bound func vals"

def main():
    assert apply_two(triple) == 6, "Function object"
    in_env(FV, 4, make_multiple_func_vals)
    return 0
