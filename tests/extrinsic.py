
Actor = DT('Actor')

Moniker = new_extrinsic('Moniker', int)

@annot('void -> int')
def go():
    actor = Actor()
    assert not has_extrinsic(Moniker, actor), "Doesn't have extrinsic"
    add_extrinsic(Moniker, actor, 3)
    assert has_extrinsic(Moniker, actor), "Has extrinsic"
    assert extrinsic(Moniker, actor) == 3, "Extrinsic"
    update_extrinsic(Moniker, actor, 4)
    assert extrinsic(Moniker, actor) == 4, "Overwritten extrinsic"
    return 0

def main():
    return scope_extrinsic(Moniker, go)
