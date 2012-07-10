@annot('void -> void')
def test():
    pass

@annot('void -> int')
def main():
    test()
    return 0
