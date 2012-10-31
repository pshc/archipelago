
def main():
    # not an actual closure yet
    @annot('void -> int noenv')
    def clos():
        return 33
    assert clos() == 33
    return 0
