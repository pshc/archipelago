from bedrock import *

@annot('void -> void')
def test():
    while True:
        break
        continue

@annot('void -> int')
def main():
    test()
    return 0
