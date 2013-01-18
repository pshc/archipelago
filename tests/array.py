from bedrock import *

Pearl = DT('Pearl')

Clam = DT('Clam', ('pearl', Pearl))

@annot('void -> [Clam]')
def gather():
    return [Clam(Pearl()), Clam(Pearl())]

def main():
    dummy = fromJust(Just("dummy")) # TEMP hack for missing bedrock dep

    empty = []
    assert len(empty) == 0, "Empty length"
    shallows = gather()
    assert len(shallows) == 2, "Heap array length"
    nothing = [Nothing(), Nothing(), Nothing()]
    null = nothing[2]
    assert len(nothing) == 3, "Array of nulls length"
    strs = ["hello", "world"]
    assert len(strs) == 2, "String array length" # this is raw currently...
    rets = [-1, -1, 0, -1]
    assert len(rets) == 4, "Raw array length"
    return rets[2]
