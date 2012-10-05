from bedrock import *

@annot('void -> void')
def test():
    while True:
        break
        continue

def main():
    test()
    return 0
