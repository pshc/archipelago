from bedrock import *

@annot('void -> int')
def main():
    a = Just(0)
    b = Nothing()
    return fromJust(a)
