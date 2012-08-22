from bedrock import *

SlimeMold = DT('SlimeMold', ('sliminess', int))

@annot('void -> int')
def main():
    a = Just(SlimeMold(0))
    b = Nothing()
    return fromJust(a).sliminess
