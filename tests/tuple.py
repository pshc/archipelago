from bedrock import *

@annot('void -> int')
def main():
    a = (4, 2)
    x = 0
    y = 0
    x, y = a
    assert x == 4, "Tuple destructuring"
    return 0
