TEST = new_env('TEST', int)

@annot('void -> int')
def read():
    assert env(TEST) == 1, "Env"
    return 0

@annot('void -> int')
def main():
    return in_env(TEST, 1, read)
