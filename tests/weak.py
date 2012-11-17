
Resource = DT('Resource', ('val', int))

WeakHolder = DT('WeakHolder', ('resource', '*Resource'))

@annot('void -> void')
def leak():
    b = Resource(0xadde)

def main():
    leak()
    res = Resource(0xfeca)
    w = WeakHolder(res)
    assert w.resource.val == 0xfeca, "Weak dereference"
    return 0
