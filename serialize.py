from base import *
from atom import *
from builtins import *

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
    assert n != sizeof(buf) - 1, "TODO: String literal is too long"
    buf[n] = char('\0')
    return (buf, n)

def read_expected(f, s):
    n = len(s)
    buf = array('char', n + 1)
    assert fread(buf, 1, n, f) == n, "Unexpected EOF"
    buf[n] = char('\0')
    assert strcmp(buf, s) == 0, "Expected %s, got %s" % (s, buf)

def read_header(f):
    read_expected(f, '"";4\n1;1\n"')
    nm, nmlen = read_str(f)
    read_expected(f, "\n2;1\n")
    ln, nl1 = read_int(f, fgetc(f))
    assert nl1 == char('\n'), "read_header: Expected newline (#1)"
    read_expected(f, "3;")
    ndeps, nl2 = read_int(f, fgetc(f))
    assert nl2 == char('\n'), "read_header: Expected newline (#2)"
    ds = array('str', ndeps)
    for i in range(ndeps):
        assert fgetc(f) == char('"'), "read_header: Expected string"
        d, dlen = read_str(f)
        ds[i] = d
        assert fgetc(f) == char('\n'), "read_header: Expected newline (#3)"
    read_expected(f, "4;")
    nroots, nl4 = read_int(f, fgetc(f))
    assert nl4 == char('\n'), "read_header: Expected newline (#4)"
    return (nm, ln, ndeps, ds, nroots)

def read_atom(f, ix, natoms, atoms, dmods):
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
    elif (char('0') <= c and c <= char('9')) or c == char('-'):
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
        i, c = read_int(f, char('0'))
        assert c == char(' '), "read_atom: Expected space in ref"
        m, c = read_int(f, char('0'))
        atom._ix = 3
        atom.val = i
        atom.ptr = to_void(dmods[m])
    else:
        assert False, "read_atom: Bad atom type '%s'" % (c,)
    subcount = 0
    if c == char(';'):
        subcount, c = read_int(f, char('0'))
    assert c == char('\n'), "read_atom: Expected newline"
    for i in range(subcount):
        ix = read_atom(f, ix, natoms, atoms, dmods)
    atom.nsubs = subcount
    return ix

Module = DT('Module', ('modName', 'str'), ('modDigest', 'str'),
                      ('modAtomCount', 'int'), ('modAtoms', 'array(Atom)'),
                      ('modRoots', 'array(int)'))

loaded_modules = {}

def load_module(digest):
    #f = fopen("mods/%s" % (digest,), "r")
    f = fopen("mods/serialize.py", "r")
    nm, ln, ndeps, ds, nroots = read_header(f)
    dmods = array('Module', ndeps + 1)
    for i in range(ndeps):
        d = ds[i]
        dmods[i + 1] = loaded_modules[d] if d in loaded_modules \
                                         else load_module(d)
    rs = array('Atom', nroots)
    atoms = array('Atom', ln + 1)
    mod = Module(nm, digest, ln, atoms, rs)
    dmods[0] = mod
    ix = 7 + ndeps
    for i in range(nroots):
        rs[i] = ix + 1
        ix = read_atom(f, ix, ln, atoms, dmods)
    #root, natoms = read_atom(f, mod, 0, {})
    fclose(f)
    #nm, ln, ds, rs = match(root,
    #    ('Str("", cons(Int(1, cons(Str(nm, _), _)), \
    #              cons(Int(2, cons(Int(ln, _), _)), \
    #              cons(Int(3, sized(every(ds, Str(d, _)))) \
    #              cons(Int(4, sized(rs)), _)))))', tuple4))
    assert ix == ln, "load_module: Atom count mismatch"
    loaded_modules[digest] = mod
    return mod

load_module('')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
