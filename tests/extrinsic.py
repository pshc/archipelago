
Actor = DT('Actor')

Moniker = new_extrinsic('Moniker', int)

@annot('void -> int')
def go():
    actor = Actor()
    add_extrinsic(Moniker, actor, 3)
    assert extrinsic(Moniker, actor) == 3
    return 0

@annot('void -> int')
def main():
    return scope_extrinsic(Moniker, go)
