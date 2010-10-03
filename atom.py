#!/usr/bin/python
from os import system
from hashlib import sha256
from base import *
from builtins import builtins
from types_builtin import *
from stdlib import *

# Bootstrap module
boot_mod = Module('bootstrap', None, [])
_b_symbol = Ref(None, boot_mod, [Ref(None, boot_mod, [Str('symbol', [])])])
_b_name = Ref(_b_symbol, boot_mod, [Ref(None, boot_mod, [Str('name', [])])])
_b_symbol.refAtom = _b_symbol
_b_symbol.subs[0].refAtom = _b_name
_b_name.subs[0].refAtom = _b_name
boot_syms = boot_mod.roots
boot_syms += [_b_symbol, _b_name]
boot_sym_names = {'symbol': _b_symbol, 'name': _b_name}
boot_sym_names_rev = {_b_symbol: 'symbol', _b_name: 'name'}

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

def _fix_type(t):
    return t() if isinstance(t, type) else t

def builtin_type_to_atoms(name):
    t = builtins_types.get(name)
    if t is None:
        return None
    if isinstance(t, tuple):
        if None in t:
            return None
        t = map(_fix_type, t)
        t = TFunc(t[:-1], t[-1])
    else:
        t = _fix_type(t)
    tvars = {}
    def builtin_typevar(v):
        index = match(v, ('TVar(Int(n, _))', identity))
        if index not in tvars:
            tvars[index] = symref('typevar', [symname(chr(96 + index))])
        return TVar(tvars[index])
    t = map_type_vars(builtin_typevar, t)
    return scheme_to_atoms(Scheme(tvars.values(), t))

def add_sym(name, extra_prop=None, extra_str=None):
    if name not in boot_sym_names:
        subs = [Ref(_b_name, boot_mod, [Str(name, [])])]
        t = builtin_type_to_atoms(name)
        if t is not None:
            subs.append(t)
        node = Ref(_b_symbol, boot_mod, subs)
        boot_syms.append(node)
        boot_sym_names[name] = node
        boot_sym_names_rev[node] = name
    else:
        subs = boot_sym_names[name].subs
    if extra_prop and boot_sym_names[extra_prop] not in subs:
        ss = [Str(extra_str, [])] if extra_str else []
        subs.append(symref(extra_prop, ss))

def type_to_atoms(t):
    return match(t,
        ("TVar(a)", lambda a: Ref(a, None, [])),
        ("TInt()", lambda: symref('int', [])),
        ("TStr()", lambda: symref('str', [])),
        ("TChar()", lambda: symref('char', [])),
        ("TBool()", lambda: symref('bool', [])),
        ("TVoid()", lambda: symref('void', [])),
        ("TNullable(v)", lambda v: symref('nullable', [type_to_atoms(v)])),
        ("TTuple(ts)", lambda ts: symref('tuple', [int_len(ts)]
            + [type_to_atoms(a) for a in ts])),
        ("TAnyTuple()", lambda: symref('tuple*', [])),
        ("TFunc(a, r)", lambda args, r: symref('func', [Int(len(args)+1, [])]
            + [type_to_atoms(a) for a in args] + [type_to_atoms(r)])),
        ("TData(a)", lambda a: Ref(a, None, [])))

def scheme_to_atoms(t):
    s = symref('type', [type_to_atoms(t.schemeType)] + list(t.schemeVars))
    return s

def atoms_to_type(a):
    return match(a,
        ("Ref(v==key('typevar'), _, _)", TVar),
        ("Ref(d==key('DT'), _, _)", TData),
        ("key('int')", lambda: TInt()),
        ("key('str')", lambda: TStr()),
        ("key('char')", lambda: TChar()),
        ("key('bool')", lambda: TBool()),
        ("key('void')", lambda: TVoid()),
        ("key('nullable', cons(v, _))",
            lambda v: TNullable(atoms_to_type(v))),
        ("key('tuple', sized(ts))", lambda ts:
            TTuple([atoms_to_type(t) for t in ts])),
        ("key('tuple*')", lambda: TAnyTuple()),
        ("key('func', sized(args))", lambda args:
            TFunc([atoms_to_type(arg) for arg in args[:-1]],
                atoms_to_type(args[-1]))))

def atoms_to_scheme(a):
    t, vs = match(a,
            ("key('type', cons(t, all(vs, v==key('typevar'))))", tuple2))
    return Scheme(vs, atoms_to_type(t))

add_sym('length')
add_sym('deps')
add_sym('roots')
add_sym('type')
add_sym('instantiation')
map(add_sym, 'void,nullable,int,bool,char,str,tuple,func,typevar'.split(','))
add_sym('tuple*')
map(add_sym, builtins)

def walk_atoms(atoms, ret, f):
    for atom in atoms:
        ret = f(atom, ret)
        ret = walk_atoms(atom.subs, ret, f)
    return ret

char_escapes = dict(zip('"\n\\\t\r\0\b\a\f\v', '"n\\tr0bafv'))

def escape_str(s):
    return '"%s"' % (''.join('\\' + char_escapes[c] if c in char_escapes
                             else c for c in s),)

def serialize_module(module):
    already_serialized = module.digest is not None
    def init_serialize(atom, (natoms, selfindices, modset)):
        assert hasattr(atom, 'subs'), "Expected atom, got: %s" % (atom,)
        selfindices[atom] = natoms
        m = getattr(atom, 'refMod', None)
        if m is not None and m is not module:
            modset.add(m)
        return (natoms + 1, selfindices, modset)
    beg = (0, {}, set())
    (natoms, atomixs, modset) = walk_atoms(module.roots, beg, init_serialize)
    nmods = len(modset)
    base = 7 + nmods
    natoms += base
    refmap = {}
    selfixs = {}
    for atom, i in atomixs.iteritems():
        refmap[atom] = "s%d" % (i + base + 1,)
        selfixs[atom] = i + base + 1
    if already_serialized:
        print '%s is already serialized' % (module.name,)
        return selfixs
    deps = ""
    for m, mod in enumerate(modset):
        ixs = serialize_module(mod)
        assert mod.digest
        for atom, i in ixs.iteritems():
            refmap[atom] = "r%d %d" % (i, m + 1)
        deps += escape_str(mod.digest) + "\n"
    nroots = len(module.roots)
    header = '"";4\n1;1\n%s\n2;1\n%d\n3%s\n%s4%s\n' % (
             escape_str(module.name), natoms, ";%d" % nmods if nmods else "",
             deps, ";%d" % nroots if nroots else "")
    hash = sha256(header)
    temp = '/tmp/serialize'
    f = file(temp, 'wb')
    f.write(header)
    def output(str):
        hash.update(str)
        f.write(str)
    def serialize_atom(atom):
        match(atom, ("Int(i, _)", lambda i: output(str(i))),
                    ("Str(s, _)", lambda s: output(escape_str(s))),
                    ("Ref(r, _, _)", lambda r: output(refmap[r])))
        n = len(atom.subs)
        output(";%d\n" % n if n else "\n")
        for sub in atom.subs:
            serialize_atom(sub)
    for atom in module.roots:
        serialize_atom(atom)
    f.close()
    module.digest = hash.digest().encode('hex')
    system('mv -f -- %s mods/%s' % (temp, module.digest))
    system('ln -sf -- %s mods/%s' % (module.digest, module.name))
    return selfixs

def write_mod_repr(filename, m, overlays):
    with file(filename, 'w') as f:
        for r in m.roots:
            f.write(repr(r))

@matcher('sized')
def _match_sized(atom, ast):
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
def _match_key(atom, ast):
    assert 1 <= len(ast.args) <= 2
    if isinstance(atom, Ref):
        key = boot_sym_names_rev.get(atom.refAtom)
        if key is not None:
            m = match_try(key, ast.args[0])
            if m is None or len(ast.args) == 1:
                return m
            msubs = match_try(atom.subs, ast.args[1])
            return None if msubs is None else m + msubs
    return None

@matcher('named')
def _match_named(atom, ast):
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

@matcher('subs')
def _match_subs(atom, ast):
    assert len(ast.args) == 1
    return match_try(atom.subs, ast.args[0]) if hasattr(atom, 'subs') else None

def _do_repr(s, r, indent):
    if hasattr(s, 'refAtom'):
        label = '<ref>'
        if s.refMod is boot_mod:
            label = s.refAtom.subs[0].subs[0].strVal
        elif hasattr(s.refAtom, 'strVal'):
            label = '->%r' % (s.refAtom.strVal,)
        elif getattr(s.refAtom, 'subs', []):
            for sub in s.refAtom.subs:
                if getattr(sub, 'refAtom', None) is _b_name:
                    label = '->%s' % (sub.subs[0].strVal,)
                    if getattr(s.refAtom, 'refMod', None) is boot_mod:
                        label = '%s (%s)' % (label,
                                s.refAtom.refAtom.subs[0].subs[0].strVal)
                    # TEMP
                    label = '%s @%x' % (label, id(s.refAtom))
                    break
        else:
            assert isinstance(s.refAtom, basestring
                    ), "Unexpected %r::%s as refAtom" % (
                    s.refAtom, type(s.refAtom).__name__)
            label = '->[missing %s]' % s.refAtom
    elif hasattr(s, 'intVal'):
        label = str(s.intVal)
    elif hasattr(s, 'strVal'):
        label = repr(s.strVal)
    else:
        label = repr(type(s))
    r.append('  ' * indent + label)
    if hasattr(s, 'subs'):
        assert isinstance(s.subs, list), "Expected list, not %s" % (s.subs,)
        for sub in s.subs:
            _do_repr(sub, r, indent + 1)

def atom_repr(s):
    r = []
    _do_repr(s, r, 0)
    r.append('')
    return '\n'.join(r)

Int.__repr__ = Str.__repr__ = Ref.__repr__ = atom_repr

if __name__ == '__main__':
    system('rm -f -- mods/*')
    mod = Module("boot", "", [Int(42, [])])
    serialize_module(mod)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
