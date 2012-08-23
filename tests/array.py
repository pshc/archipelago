from bedrock import *

@annot('void -> int')
def main():
    empty = []
    assert len(empty) == 0, "Empty length"
    strs = ["hello", "world"]
    assert len(strs) == 2, "Pointer array length"
    rets = [-1, -1, 0, -1]
    assert len(rets) == 4, "Array length"
    return rets[2]
