@annot('int -> int')
def ignored(n):
    assert n == 4
    return n

@annot('void -> int')
def main():
    _ = ignored(4)
    return 0
