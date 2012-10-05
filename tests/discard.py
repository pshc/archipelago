@annot('int -> int')
def ignored(n):
    assert n == 4
    return n

def main():
    _ = ignored(4)
    return 0
