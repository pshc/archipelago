
Isle = DT('Isle', ('area', int))

def main():
    isle = Isle(1)
    assert isle.area == 1, "Ctor initialization"
    isle.area = 0
    return isle.area
