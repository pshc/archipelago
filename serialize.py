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

def escape(s):
    slen = len(s)
    buf = array('char', 81)
    si = 0
    n = 0
    while si < slen and n < sizeof(buf) - 1:
        c = s[si]
        if c in escape_dest:
            for i in range(len(escape_dest)):
                if c == escape_dest[i]:
                    buf[n] = char('\\')
                    buf[n+1] = escape_src[i]
                    n += 1
                    break
        else:
            buf[n] = c
        n += 1
        si += 1
    assert n != sizeof(buf) - 1, "TODO: String literal %s is too long" % buf
    buf[n] = char('\0')
    return hint(stringify(buf))

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
    return (hint(stringify(buf)), n)

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

def set_atom_str(atom, s, length, has_subs, next_sibling):
    atom._ix = 1
    atom.val = length
    atom.ptr = to_void(s)
    atom.hassubs = has_subs
    atom.nsibling = next_sibling

def set_atom_int(atom, n, has_subs, next_sibling):
    atom._ix = 0
    atom.val = n
    atom.ptr = None
    atom.hassubs = has_subs
    atom.nsibling = next_sibling

def set_atom_ref(atom, ix, mod, has_subs, next_sibling):
    atom._ix = 2
    atom.val = ix
    atom.ptr = to_void(mod)
    atom.hassubs = has_subs
    atom.nsibling = next_sibling

def fill_header(nm, ln, ndeps, ds, nroots, atoms):
    set_atom_str(atoms[1], "", 0, True, 0)
    set_atom_int(atoms[2], 1, True, 4)
    set_atom_str(atoms[3], nm, len(nm), False, 0)
    set_atom_int(atoms[4], 2, True, 6)
    set_atom_int(atoms[5], ln, False, 0)
    set_atom_int(atoms[6], 3, ndeps != 0, 7 + ndeps)
    for i in range(ndeps):
        d = ds[i]
        set_atom_str(atoms[7 + i], d, len(d), False, 0 if i==ndeps-1 else i+1)
    set_atom_int(atoms[7 + ndeps], 4, nroots != 0, 0)
    return 7 + ndeps

def read_atom(f, ix, natoms, atoms, dmods):
    c = fgetc(f)
    atom = None
    ix += 1
    atom = atoms[ix]
    if c == char('"'):
        s, slen = read_str(f)
        set_atom_str(atom, s, slen, False, 0)
        c = fgetc(f)
    elif (char('0') <= c and c <= char('9')) or c == char('-'):
        i, c = read_int(f, c)
        set_atom_int(atom, i, False, 0)
    elif c == char('s'):
        i, c = read_int(f, char('0'))
        set_atom_ref(atom, i, dmods[0], False, 0)
    elif c == char('r'):
        i, c = read_int(f, char('0'))
        assert c == char(' '), "read_atom: Expected space in ref"
        m, c = read_int(f, char('0'))
        set_atom_ref(atom, i, dmods[m], False, 0)
    else:
        assert False, "read_atom: Bad atom type '%c'" % (c,)
    subcount = 0
    if c == char(';'):
        subcount, c = read_int(f, char('0'))
        atom.hassubs = True
    assert c == char('\n'), "read_atom: Expected newline, got '%c'" % (c,)
    # prev and this are for the sibling linked list
    prev = None
    for i in range(subcount):
        this = ix + 1
        ix = read_atom(f, ix, natoms, atoms, dmods)
        if prev is not None:
            prev.nsibling = this
        prev = atoms[this]
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
    # Actually read the root atoms, tracking the sibling linked list
    prev = None
    for i in range(nroots):
        this = ix + 1
        rs[i] = this
        ix = read_atom(f, ix, ln, atoms, dmods)
        if prev is not None:
            prev.nsibling = this
        prev = atoms[this]
    fclose(f)
    assert ix == ln, "load_module: Atom count mismatch"
    loaded_modules[digest] = mod
    return mod

def scan_atoms(atom, ix, own_atoms, ds):
    own_atoms[atom] = ix
    ix += 1
    mod, subs = match(atom, ('Int(_, s)', lambda s: (None, s)),
                            ('Str(_, s)', lambda s: (None, s)),
                            ('Ref(_, m, s)', tuple2))
    if mod is not None:
        ds[mod.modDigest] = mod
    for sub in subs:
        ix = scan_atoms(sub, ix, own_atoms, ds)
    return ix

def data_line(data, line):
    fwrite(data[0], line)
    fputc(data[0], '\n')
    sha256_update(data[1], line)
    sha256_update(data[1], '\n')

def ref_str(atom, mod, own_atoms, own_offset, depixs):
    assert mod is None and atom in own_atoms, "Only self-refs implemented"
    return "s%d" % (own_atoms[atom] + own_offset,)

def write_atom(atom, own_atoms, own_offset, data, depixs):
    s, ss = match(atom, ('Int(i, ss)', lambda i, ss: ("%d" % (i,), ss)),
                        ('Str(s, ss)', lambda s, ss: ('"%s"'%(escape(s),),ss)),
                        ('Ref(a, m, ss)', lambda a, m, ss:
            (ref_str(a, m, own_atoms, own_offset, depixs), ss)))
    nsubs = len(ss)
    if nsubs > 0:
        s = "%s;%d" % (s, nsubs)
    data_line(data, s)
    for sub in ss:
        write_atom(sub, own_atoms, own_offset, data, depixs)

def save_module(name, mod_roots):
    ds = {}
    own_atoms = {}
    print 'scanning for deps'
    natoms = 0
    for r in mod_roots:
        natoms = scan_atoms(r, natoms, own_atoms, ds)
    offset = 7 + len(ds)
    natoms += offset
    print 'natoms: %d' % natoms
    depixs = {}
    print 'adding deps'
    dep_digests = dict_keys(ds)
    list_sort(dep_digests)
    ix = 1
    for dep in dep_digests:
        depmod = ds[dep]
        depixs[depmod] = ix
        ix += 1
    header = Str("", [Int(1, [Str(name, [])]),
                      Int(2, [Int(natoms, [])]),
                      Int(3, [Str(d, []) for d in dep_digests]),
                      Int(4, mod_roots)])
    temp = "/tmp/serialize"
    data = (fopen(temp, 'wb'), sha256())
    print 'writing'
    write_atom(header, own_atoms, offset + 1, data, depixs)
    fclose(data[0])
    digest = sha256_hexdigest(data[1])
    system('mv -f -- %s mods/%s' % (temp, digest))
    system('ln -s -- %s mods/%s' % (digest, name))
    return digest

def print_atom(atom, indent):
    t, ss = match(atom, ("Str(s, ss)", tuple2),
                        ("Int(n, ss)", tuple2),
                        ("Ref(r, m, ss)", lambda r, m, ss: ("ref", ss)))
    print "%s%s" % ('  ' * indent, t)
    for s in ss:
        print_atom(s, indent + 1)

#test_mod = load_module("test.py")
#print 'name: %s' % (test_mod.modName,)
#print '#atoms: %d' % (test_mod.modAtomCount,)
#print test_mod.modAtoms
#print_atom((test_mod, 1), 0)

print 'saving...'
own = Str('world', [])
print save_module('helloworld', [Str('hello\n',
    [own, Int(33, []), Ref(own, None, [])])])

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
