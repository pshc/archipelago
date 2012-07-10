from bedrock import *

@annot('void -> int')
def main():
    double_ = lambda x: x * 2
    assert double_(88) == 176
    return double_(0)
