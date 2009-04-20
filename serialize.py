from base import *
from atom import *

def read_int(f, first):
    neg = False
    num = 0
    if first == char('-'):
        neg = True
    else:
        num += first - char('0')
    c = fgetc(f)
    while char('0') <= c and c <= char('9'):
        num = num * 10 + (char('0') - c if neg else c - char('0'))
        c = fgetc(f)
    return num, c

escape_src = r'"n\tr0bafv'
escape_dest = '"\n\\\t\r\0\b\a\f\v'

def read_str(f):
    buf = array('char', 81)
    n = 0
    while n < sizeof(buf) - 1: # TODO: utf-8
        c = fgetc(f)
        if c == char('"'):
            break
        elif c == char('\\'):
            c = fgetc(f)
            for i in range(len(escape_src)):
                if c == escape_src[i]:
                    c = escape_dest[i]
                    break
        buf[n] = c
        n += 1
    assert n != sizeof(buf) - 1
    buf[n] = char('\0')
    return (buf, n)

def read_expected(f, s):
    n = len(s)
    buf = array('char', n + 1)
    assert fread(buf, 1, n, f) == n
    buf[n] = char('\0')
    assert buf == s

def read_header(f):
    read_expected(f, '"";4\n1;1\n"')
    nm, nmlen = read_str(f)
    read_expected(f, "\n2;1\n")
    ln, nl1 = read_int(f, fgetc(f))
    assert nl1 == char('\n')
    read_expected(f, "3;")
    ndeps, nl2 = read_int(f, fgetc(f))
    assert nl2 == char('\n')
    ds = array('str', ndeps)
    for i in range(ndeps):
        assert fgetc(f) == char('"')
        d, dlen = read_str(f)
        ds[i] = d
        assert fgetc(f) == char('\n')
    read_expected(f, "4;")
    nroots, nl3 = read_int(f, fgetc(f))
    assert nl3 == char('\n')
    return (nm, ln, ndeps, ds, nroots)

def read_atom(f, ix, atoms, dmods):
    c = fgetc(f)
    subs = []
    atom = None
    ix += 1
    atom = atoms[ix]
    if c == char('"'):
        s, slen = read_str(f)
        atom._ix = 2
        atom.val = slen
        atom.ptr = to_void(s)
    elif char('0') <= c <= char('9') or c == '-':
        i, c = read_int(f, c)
        atom._ix = 1
        atom.val = i
        atom.ptr = None
    elif c == char('s'):
        i, c = read_int(f, char('0'))
        atom._ix = 3
        atom.val = i
        atom.ptr = to_void(dmods[0])
    elif c == char('r'):
        ix, c = read_int(f, char('0'))
        assert c == char(' ')
        m, c = read_int(f, char('0'))
        atom._ix = 3
        atom.val = i
        atom.ptr = to_void(dmods[m])
    else:
        assert False, "Bad atom"
    subcount = 0
    if c == char(';'):
        subcount, c = read_int(f, char('0'))
    assert c == char('\n')
    for i in range(subcount):
        ix = read_atom(f, ix, atoms, dmods)
    atom.nsubs = subcount
    return ix

loaded_modules = {}

def load_module(digest):
    f = fopen("mods/%s" % (digest,), "r")
    nm, ln, ndeps, ds, nroots = read_header(f)
    dmods = array('Module', ndeps + 1)
    for i in range(ndeps):
        d = ds[i]
        dmods[i + 1] = loaded_modules[d] if d in loaded_modules \
                                         else load_module(d)
    rs = array('Atom', nroots)
    mod = Module(nm, digest, rs)
    dmods[0] = mod
    ln -= 7 + ndeps
    atoms = array('Atom', ln + 1)
    ix = 0
    for i in range(nroots):
        rs[i] = ix + 1
        ix = read_atom(f, ix, atoms, dmods)
    #root, natoms = read_atom(f, mod, 0, {})
    fclose(f)
    #nm, ln, ds, rs = match(root,
    #    ('Str("", cons(Int(1, cons(Str(nm, _), _)), \
    #              cons(Int(2, cons(Int(ln, _), _)), \
    #              cons(Int(3, sized(every(ds, Str(d, _)))) \
    #              cons(Int(4, sized(rs)), _)))))', tuple4))
    assert ix == ln
    loaded_modules[d] = digest
    return mod

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
