from bedrock import *

SlimeMold = DT('SlimeMold', ('sliminess', int))

def main():
    a = Just(SlimeMold(0))
    b = Nothing()
    assert isJust(a), "isJust"
    c = Just([99])
    assert fromJust(c)[0] == 99
    return fromJust(a).sliminess
