
Isle = DT('Isle', ('area', int))

@annot('void -> int')
def main():
    isle = Isle(1)
    isle.area = 0
    return isle.area
