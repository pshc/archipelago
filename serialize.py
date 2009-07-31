from base import *
from atom import *
from builtins import *

def read_int(f, first):
    neg = False
    num = 0
    if first == char('-'):
        neg = True
    else:
        num += ord(first) - ord(char('0'))
    c = fgetc(f)
    while char('0') <= c and c <= char('9'):
        num = num * 10 + (ord(char('0')) - ord(c) if neg
                          else ord(c) - ord(char('0')))
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
    assert n != sizeof(buf) - 1, "TODO: String literal %s is too long" % buf
    buf[n] = char('\0')
    buf = hint(stringify(buf))
    return (buf, n)

def read_expected(f, s):
    n = len(s)
    buf = array('char', n + 1)
    assert fread(buf, 1, n, f) == n, "Unexpected EOF"
    buf[n] = char('\0')
    buf = hint(stringify(buf))
    assert buf == s, 'Expected "%s", got "%s"' % (s, buf)

module_header = '"";4\n1;1\n"%s"\n2;1\n%d\n3;%d'

def read_header(f):
    read_expected(f, '"";4\n1;1\n"')
    nm, nmlen = read_str(f)
    read_expected(f, "\n2;1\n")
    ln, nl = read_int(f, fgetc(f))
    assert nl == char('\n'), "read_header: Expected newline (#1)"
    assert fgetc(f) == char('3'), "read_header: Expected '3'"
    ndeps = 0
    nl = fgetc(f)
    if nl == char(';'):
        ndeps, nl = read_int(f, fgetc(f))
    assert nl == char('\n'), "read_header: Expected newline (#2)"
    ds = array('str', ndeps)
    for i in range(ndeps):
        assert fgetc(f) == char('"'), "read_header: Expected string"
        d, dlen = read_str(f)
        ds[i] = d
        assert fgetc(f) == char('\n'), "read_header: Expected newline (#3)"
    read_expected(f, "4;")
    nroots, nl = read_int(f, fgetc(f))
    assert nl == char('\n'), "read_header: Expected newline (#4)"
    return (nm, ln, ndeps, ds, nroots)

def set_atom_str(atom, s, length, nchildren):
    atom._ix = 1
    atom.val = length
    atom.ptr = to_void(s)
    atom.nsubs = nchildren

def set_atom_int(atom, n, nchildren):
    atom._ix = 0
    atom.val = n
    atom.ptr = None
    atom.nsubs = nchildren

def set_atom_ref(atom, ix, mod, nchildren):
    atom._ix = 2
    atom.val = ix
    atom.ptr = to_void(mod)
    atom.nsubs = nchildren

def fill_header(nm, ln, ndeps, ds, nroots, atoms):
    set_atom_str(atoms[1], "", 0, 4)
    set_atom_int(atoms[2], 1, 1)
    set_atom_str(atoms[3], nm, len(nm), 0)
    set_atom_int(atoms[4], 2, 1)
    set_atom_int(atoms[5], ln, 0)
    set_atom_int(atoms[6], 3, ndeps)
    for i in range(ndeps):
        d = ds[i]
        set_atom_str(atoms[7 + i], d, len(d), 0)
    set_atom_int(atoms[7 + ndeps], 4, nroots)
    return 7 + ndeps

def read_atom(f, ix, natoms, atoms, dmods):
    c = fgetc(f)
    subs = []
    atom = None
    ix += 1
    atom = atoms[ix]
    if c == char('"'):
        s, slen = read_str(f)
        set_atom_str(atom, s, slen, 0)
        c = fgetc(f)
    elif (char('0') <= c and c <= char('9')) or c == char('-'):
        i, c = read_int(f, c)
        set_atom_int(atom, i, 0)
    elif c == char('s'):
        i, c = read_int(f, char('0'))
        set_atom_ref(atom, i, dmods[0], 0)
    elif c == char('r'):
        i, c = read_int(f, char('0'))
        assert c == char(' '), "read_atom: Expected space in ref"
        m, c = read_int(f, char('0'))
        set_atom_ref(atom, i, dmods[m], 0)
    else:
        assert False, "read_atom: Bad atom type '%c'" % (c,)
    subcount = 0
    if c == char(';'):
        subcount, c = read_int(f, char('0'))
    assert c == char('\n'), "read_atom: Expected newline, got '%c'" % (c,)
    for i in range(subcount):
        ix = read_atom(f, ix, natoms, atoms, dmods)
    atom.nsubs = subcount
    return ix

Module = DT('Module', ('modName', 'str'), ('modDigest', 'str'),
                      ('modAtomCount', 'int'), ('modAtoms', 'array(Atom)'),
                      ('modRoots', 'array(int)'))

loaded_modules = {}

def load_module(digest):
    f = fopen("mods/%s" % (digest,), "rb")
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
    ix = fill_header(nm, ln, ndeps, ds, nroots, atoms)
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

def scan_atoms(atom, orig_module, deps):
    mod, subs = match(mod, ('Int(_, s)', lambda s: (None, s)),
                           ('Str(_, s)', lambda s: (None, s)),
                           ('Ref(_, m, s)', tuple2))
    if mod is not None and mod is not orig_module:
        if mod.modDigest is None:
            save_module(mod)
        deps[mod.modDigest] = mod
    natoms = 1
    for sub in subs:
        natoms += scan_atoms(sub, orig_module, deps)
    return natoms

def data_line(data, line):
    fwrite(data[0], line)
    fputc(data[0], '\n')
    data[1].update(line)
    data[1].update('\n')

def write_atom(ix, atoms, data, depixs):
    pass

def save_module(mod):
    nm, dg, ln, atoms, rs = match(mod, ("Module(n, d, l, a, r)", tuple5))
    if dg is not None:
        return
    natoms = 7
    deps = {}
    for r in rs:
        natoms += scan_atoms(atoms[r-1], mod, deps)
    ndeps = len(deps)
    natoms += ndeps
    temp = "/tmp/serialize"
    data = (fopen(temp, 'wb'), sha256())
    data_line(data, module_header % (nm, natoms, ndeps))
    depixs = {}
    ix = 1
    for dep in sorted(deps.keys()):
        data_line(data, '"%s"' % (dep.modDigest,))
        depixs[dep] = ix
        ix += 1
    nroots = len(rs)
    data_line(data, '4;%d' % (nroots,))
    for r in rs:
        write_atom(r, atoms, data, depixs)
    fclose(data[0])
    digest = data[1].hexdigest()
    system('mv -f -- %s mods/%s' % (temp, digest))
    system('ln -s -- %s mods/%s' % (digest, nm))
    mod.modAtomCount = natoms
    mod.modDigest = digest

def print_atom(atom, indent):
    t, ss = match(atom, ("Str(s, ss)", tuple2),
                        ("Int(n, ss)", tuple2),
                        ("Ref(r, m, ss)", lambda r, m, ss: ("ref", ss)))
    print "%s%s" % ('  ' * indent, t)
    for s in ss:
        print_atom(s, indent + 1)

test_mod = load_module("test.py")
print test_mod.modAtoms
print_atom((test_mod, 1), 0)

load_module("serialize.py")

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
