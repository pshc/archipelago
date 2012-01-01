
Resource = DT('Resource', ('val', int))

WeakHolder = DT('WeakHolder', ('resource', '*Resource'))

def main():
    res = Resource(12)
    w = WeakHolder(res)
    assert w.resource.val == 12, "Weak dereference"
    return 0
