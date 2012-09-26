TEST = new_env('TEST', int)
BOGUS = new_env('BOGUS', int)

@annot('void -> int')
def square_env():
    return env(TEST) * env(TEST)

@annot('int -> int')
def again(nine):
    assert env(TEST) == 1, "Env inside"
    return in_env(TEST, nine, square_env)

@annot('void -> void')
def read():
    assert have_env(TEST), "Inside env"
    assert not have_env(BOGUS), "Outside env"
    assert env(TEST) == 1, "Env"
    assert again(9) == 81, "Env param/ret passing"

@annot('void -> int')
def read2():
    assert have_env(TEST), "Inside second env"
    assert env(TEST) == 2, "Second env"
    return 0

@annot('void -> int')
def main():
    in_env(TEST, 1, read)
    return in_env(TEST, 2, read2)
