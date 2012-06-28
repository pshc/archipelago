TEST = new_env('TEST', int)

@annot('void -> void')
def read():
    assert have_env(TEST), "Inside env"
    assert env(TEST) == 1, "Env"

@annot('void -> int')
def read2():
    assert have_env(TEST), "Inside env"
    assert env(TEST) == 2, "Env"
    return 0

@annot('void -> int')
def main():
    assert not have_env(TEST), "Outside env"
    in_env(TEST, 1, read)
    return in_env(TEST, 2, read2)
