#!/usr/bin/python
from os import system
from hashlib import sha256
from base import *

(Atom, Int, Str, Ref) = ADT('Atom',
                            'Int', ('intVal', int), ('subs', ['Atom']),
                            'Str', ('strVal', str), ('subs', ['Atom']),
                            'Ref', ('refAtom', 'Atom'), ('refMod', 'Module'),
                                   ('subs', ['Atom']))

Module = DT('Module',
            ('name', str), ('digest', str), ('roots', [Atom]))

def walk_atoms(atoms, ret, f):
    for atom in atoms:
        ret = f(atom, ret)
        ret = walk_atoms(atom.subs, ret, f)
    return ret

def serialize_module(module):
    beg = (7, {}, set())
    (natoms, selfixs, modset) = walk_atoms(module.roots, beg, init_serialize)
    nmods = len(modset)
    natoms += nmods
    refmap = {}
    for (i, ix) in enumerate(selfixs):
        refmap[ix] = (i + 1, 0)
    deps = ""
    for (m, mod) in enumerate(modset):
        ixs = serialize_module(mod)
        assert len(mod.digest)
        for (i, ix) in enumerate(ixs):
            refmap[ix] = (i + 1, m + 1)
        deps += "s%s\n" % repr(mod.digest)
    nroots = len(module.roots)
    header = 's"";4\ni1;1\ns%s\ni2;1\ni%d\ni3%s\n%si4%s\n' % (
             repr(module.name), natoms, ";%d" % (nmods,) if nmods else "",
             deps, ";%d" % (nroots,) if nroots else "")
    hash = sha256(header)
    temp = '/tmp/serialize'
    f = file(temp, 'wb')
    f.write(header)
    def output(str):
        hash.update(str)
        f.write(str)
    def serialize_atom(atom):
        match(atom, ("Int(i, _)", lambda i: output("i%d" % (i,))),
                    ("Str(s, _)", lambda s: output("s%s" % (repr(s),))),
                    ("Ref(r, _, _)", lambda r: output("r%d %d" % refmap[r])))
        n = len(atom.subs)
        output(";%d\n" % n if n else "\n")
        for sub in atom.subs:
            serialize_atom(sub)
    for atom in module.roots:
        serialize_atom(atom)
    f.close()
    filename = 'mods/%s' % hash.digest().encode('hex')
    system('mv -f -- %s %s' % (temp, filename))
    return selfixs

system('rm -f -- mods/*')
mod = Module("boot", "", [Int(42, [])])
serialize_module(mod)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
