#!/usr/bin/python
from os import system
from hashlib import sha256
from base import *
from builtins import Atom, Int, Str, Ref, builtins
from types_builtin import *

Module = DT('Module',
            ('name', str), ('digest', str), ('roots', [Atom]))

# Bootstrap module
boot_mod = Module('bootstrap', None, [])
_b_symbol = Ref(None, boot_mod, [Ref(None, boot_mod, [Str('symbol', [])])])
_b_name = Ref(_b_symbol, boot_mod, [Ref(None, boot_mod, [Str('name', [])])])
_b_symbol.refAtom = _b_symbol
_b_symbol.subs[0].refAtom = _b_name
_b_name.subs[0].refAtom = _b_name
_boot_syms = boot_mod.roots
_boot_syms += [_b_symbol, _b_name]
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
        args, ret = t[:-1], t[-1]
        t = TFunc(map(_fix_type, args), _fix_type(ret))
    else:
        t = _fix_type(t)
    return scheme_to_atoms(Scheme([], t))

def add_sym(name):
    if name in boot_sym_names:
        return
    subs = [Ref(_b_name, boot_mod, [Str(name, [])])]
    t = builtin_type_to_atoms(name)
    if t is not None:
        subs.append(t)
    node = Ref(_b_symbol, boot_mod, subs)
    _boot_syms.append(node)
    boot_sym_names[name] = node
    boot_sym_names_rev[node] = name

def _fresh_tvar(num):
    nm = chr(ord('a') + num)
    return symref('typevar', [symname(nm)])

def _tvar_to_ref(n, m):
    if n not in m:
        # Just make it anyway
        m[n] = _fresh_tvar(len(m))
    return m[n]

def type_to_atoms(t, m):
    return match(t,
        ("TVar(n)", lambda n: Ref(_tvar_to_ref(n, m), None, [])),
        ("TInt()", lambda: symref('int', [])),
        ("TStr()", lambda: symref('str', [])),
        ("TChar()", lambda: symref('char', [])),
        ("TBool()", lambda: symref('bool', [])),
        ("TVoid()", lambda: symref('void', [])),
        ("TNullable()", lambda: symref('nullable', [])),
        ("TTuple(ts)", lambda ts: symref('tuple', [int_len(ts)]
            + [type_to_atoms(a, m) for a in ts])),
        ("TAnyTuple()", lambda: symref('tuple*', [])),
        ("TFunc(a, r)", lambda args, r: symref('func', [Int(len(args)+1, [])]
            + [type_to_atoms(a, m) for a in args] + [type_to_atoms(r, m)])))

def scheme_to_atoms(t):
    m = {}
    for n, v in enumerate(t.schemeVars):
        m[v.varIndex] = _fresh_tvar(n)
    s = symref('type', [type_to_atoms(t.schemeType, m)])
    s.subs += [m[k] for k in sorted(m.keys())]
    return s

def atoms_to_type(a, m):
    return match(a,
        ("Ref(v==key('typevar'), _, _)", lambda v: m[v]),
        ("key('int')", lambda: TInt()),
        ("key('str')", lambda: TStr()),
        ("key('char')", lambda: TChar()),
        ("key('bool')", lambda: TBool()),
        ("key('void')", lambda: TVoid()),
        ("key('nullable')", lambda: TNullable()),
        ("key('tuple', sized(ts))", lambda ts:
            TTuple([atoms_to_type(t, m) for t in ts])),
        ("key('tuple*')", lambda: TAnyTuple()),
        ("key('func', sized(args))", lambda args:
            TFunc([atoms_to_type(arg, m) for arg in args[:-1]],
                atoms_to_type(args[-1], m))))

def atoms_to_scheme(a):
    t, vs = match(a, ("key('type', cons(t, all(vs, key('typevar'))))", tuple2))
    tvs = [TVar(n) for n, v in enumerate(vs)]
    return Scheme(tvs, atoms_to_type(t, dict(zip(vs, tvs))))

add_sym('length')
add_sym('deps')
add_sym('roots')
add_sym('type')
map(add_sym, 'void,nullable,int,bool,char,str,tuple,func,typevar'.split(','))
add_sym('tuple*') # TEMP
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

def _do_repr(s, r, indent):
    if hasattr(s, 'refAtom'):
        label = '<ref>'
        if s.refMod is boot_mod:
            label = s.refAtom.subs[0].subs[0].strVal
        elif s.refAtom.subs:
            if getattr(s.refAtom.subs[0], 'refAtom', None) is _b_name:
                label = '->%s' % (s.refAtom.subs[0].subs[0].strVal)
    elif hasattr(s, 'intVal'):
        label = str(s.intVal)
    elif hasattr(s, 'strVal'):
        label = repr(s.strVal)
    else:
        label = repr(type(s))
    r.append('  ' * indent + label)
    if hasattr(s, 'subs'):
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
