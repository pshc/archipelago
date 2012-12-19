from bedrock import *

NoHalt = DT('NoHalt', ('loopsLeft', int))

# this is to check codegen of object destruction in a loop test expr
# (not that it's going to make a big deal if anything goes wrong...)
@annot('void -> NoHalt')
def infinity():
    return NoHalt(1)

@annot('void -> void')
def test():
    while infinity().loopsLeft > 0:
        break
        continue

def main():
    test()
    return 0
