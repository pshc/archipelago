TEST = new_env('TEST', int)

@annot('void -> int')
def read():
    assert have_env(TEST), "Inside env"
    assert env(TEST) == 1, "Env"
    return 0

@annot('void -> int')
def main():
    assert not have_env(TEST), "Outside env"
    return in_env(TEST, 1, read)
