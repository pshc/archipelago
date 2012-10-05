from bedrock import *

SlimeMold = DT('SlimeMold', ('sliminess', int))

def main():
    a = Just(SlimeMold(0))
    b = Nothing()
    assert isJust(a), "isJust"
    return fromJust(a).sliminess
