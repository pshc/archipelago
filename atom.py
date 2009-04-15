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

# Bootstrap module
boot_mod = Module('bootstrap', None, [])
b_symbol = Ref(None, boot_mod, [Ref(None, boot_mod, [Str('symbol', [])])])
b_name = Ref(b_symbol, boot_mod, [Ref(None, boot_mod, [Str('name', [])])])
b_symbol.refAtom = b_symbol
b_symbol.subs[0].refAtom = b_name
b_name.subs[0].refAtom = b_name
boot_syms = [b_symbol, b_name]
boot_sym_names = {'symbol': b_symbol, 'name': b_name}

def add_sym(name):
    if name in boot_sym_names:
        return
    node = Ref(b_symbol, boot_mod, [Ref(b_name, boot_mod, [Str(name, [])])])
    boot_syms.append(node)
    boot_sym_names[name] = node

map(add_sym, builtinConsts)
map(add_sym, builtinFuncs)

def int_len(list):
    return Int(len(list), [])

def symref(name, subs):
    assert name in boot_sym_names, '%s not a boot symbol' % (name,)
    return Ref(boot_sym_names[name], boot_mod, subs)

def symcall(name, subs):
    assert name in boot_sym_names, '%s not a boot symbol' % (name,)
    func = Ref(boot_sym_names[name], boot_mod, [])
    return symref('call', [func, int_len(subs)] + subs)

def getident(ref):
    return match(ref, ('Ref(named(nm), _, _)', identity))

def symname(name):
    return symref('name', [Str(name, [])])

def getname(sym):
    return match(sym, ('named(nm)', identity))

def walk_atoms(atoms, ret, f):
    for atom in atoms:
        ret = f(atom, ret)
        ret = walk_atoms(atom.subs, ret, f)
    return ret

def serialize_module(module):
    def init_serialize(atom, (natoms, selfindices, modset)):
        selfindices[atom] = natoms + 1
        match(atom, ("Ref(_, m, _)", modset.add),
                    ("_",            lambda: None))
        return (natoms + 1, selfindices, modset)
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

@matcher('sized')
def match_sized(atom, ast):
    # specific to atoms; matches int(n) followed by n items
    assert 1 <= len(ast.args) <= 2
    assert isinstance(atom, list), "Expected list for 'sized"
    if isinstance(atom[0], Int):
        n = atom[0].intVal
        if len(atom) > n:
            atomsm = match_try(atom[1:n+1], ast.args[0])
            if atomsm is not None:
                if len(ast.args) == 1:
                    return atomsm
                restm = match_try(atom[n+1:], ast.args[1])
                if restm is not None:
                    return atomsm + restm
    return None

@matcher('key')
def match_key(atom, ast):
    assert 1 <= len(ast.args) <= 2
    if isinstance(atom, Ref):
        if len(ast.args) == 1: # Don't know which boot sym this is yet
            for k, v in boot_sym_names.iteritems():
                if atom.refAtom is v:
                    return match_try(k, ast.args[0])
        else:
            assert isinstance(ast.args[0], compiler.ast.Const)
            if atom.refAtom is boot_sym_names[ast.args[0].value]:
                return match_try(atom.subs, ast.args[1])
    return None

@matcher('named')
def match_named(atom, ast):
    assert 1 <= len(ast.args) <= 2
    for sub in atom.subs:
        if isinstance(sub, Ref) and sub.refAtom is boot_sym_names['name']:
            name = sub.subs[0]
            assert isinstance(name, Str)
            m = match_try(name.strVal, ast.args[0])
            if len(ast.args) == 1 or m is None:
                return m
            n = match_try(atom.subs, ast.args[1])
            return None if n is None else m + n
    return None


def do_repr(s, r, indent):
    if hasattr(s, 'refAtom'):
        label = '<ref>'
        if s.refMod is boot_mod:
            label = s.refAtom.subs[0].subs[0].strVal
        elif s.refAtom.subs:
            if getattr(s.refAtom.subs[0], 'refAtom', None) is b_name:
                label = '->%s' % (s.refAtom.subs[0].subs[0].strVal)
    elif hasattr(s, 'intVal'):
        label = str(s.intVal)
    else:
        label = repr(s.strVal)
    r.append('  ' * indent + label)
    for sub in s.subs:
        do_repr(sub, r, indent + 1)

def atom_repr(s):
    r = []
    do_repr(s, r, 0)
    r.append('')
    return '\n'.join(r)

Int.__repr__ = Str.__repr__ = Ref.__repr__ = atom_repr

if __name__ == '__main__':
    system('rm -f -- mods/*')
    mod = Module("boot", "", [Int(42, [])])
    serialize_module(mod)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
