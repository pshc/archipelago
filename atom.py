#!/usr/bin/python2
from os import system
from hashlib import sha256
from base import *
from types_builtin import *
from bedrock import *

# Bootstrap module
boot_mod = Module('bootstrap', None, [])
_b_symbol = Ref(None, [Ref(None, [Str('symbol', [])])])
_b_name = Ref(_b_symbol, [Ref(None, [Str('name', [])])])
_b_symbol.refAtom = _b_symbol
_b_symbol.subs[0].refAtom = _b_name
_b_name.subs[0].refAtom = _b_name
boot_syms = boot_mod.roots
boot_syms += [_b_symbol, _b_name]
boot_sym_names = {'symbol': _b_symbol, 'name': _b_name}
boot_sym_names_rev = {_b_symbol: 'symbol', _b_name: 'name'}

loaded_modules = {}
loaded_module_atoms = {}

csym_roots = []

def int_len(list):
    return Int(len(list), [])

def symref(name, subs):
    assert name in boot_sym_names, '%s not a boot symbol' % (name,)
    return Ref(boot_sym_names[name], subs)

def symcall(name, subs):
    assert name in boot_sym_names, '%s not a boot symbol' % (name,)
    func = Ref(boot_sym_names[name], [])
    return symref('call', [func, int_len(subs)] + subs)

def getident(ref):
    return match(ref, ('Ref(named(nm), _)', identity))

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
    assert not boot_mod.digest, "Can't add symbols after bootstrap serialized"
    if name not in boot_sym_names:
        subs = [Ref(_b_name, [Str(name, [])])]
        t = builtin_type_to_atoms(name)
        if t is not None:
            subs.append(t)
        node = Ref(_b_symbol, subs)
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
        ("TVar(a)", lambda a: Ref(a, [])),
        ("TInt()", lambda: symref('int', [])),
        ("TStr()", lambda: symref('str', [])),
        ("TChar()", lambda: symref('char', [])),
        ("TBool()", lambda: symref('bool', [])),
        ("TVoid()", lambda: symref('void', [])),
        ("TTuple(ts)", lambda ts: symref('tuple', [int_len(ts)]
            + [type_to_atoms(a) for a in ts])),
        ("TAnyTuple()", lambda: symref('tuple*', [])),
        ("TFunc(a, r)", lambda args, r: symref('func', [Int(len(args)+1, [])]
            + [type_to_atoms(a) for a in args] + [type_to_atoms(r)])),
        ("TData(a)", lambda a: Ref(a, [])),
        ("TApply(t, ss)", lambda t, ss: symref('typeapply',
            [type_to_atoms(t), int_len(ss)] + map(type_to_atoms, ss))))

def scheme_to_atoms(t):
    s = symref('type', [type_to_atoms(t.schemeType)] + list(t.schemeVars))
    return s

def atoms_to_type(a):
    return match(a,
        ("Ref(v==key('typevar'), _)", TVar),
        ("Ref(d==key('DT'), _)", TData),
        ("key('typeapply', cons(t, sized(ss)))",
            lambda t, ss: TApply(atoms_to_type(t), map(atoms_to_type, ss))),
        ("key('int')", lambda: TInt()),
        ("key('str')", lambda: TStr()),
        ("key('char')", lambda: TChar()),
        ("key('bool')", lambda: TBool()),
        ("key('void')", lambda: TVoid()),
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

def load_module_dep(filename, deps):
    assert filename.endswith('.py')
    name = filename.replace('/', '_')[:-3]
    if name in loaded_modules:
        mod = loaded_modules[name]
        deps.add(mod)
        return mod
    from ast import convert_file
    mod = convert_file(filename, name, deps)
    write_mod_repr('views/' + name + '.txt', mod, [])
    serialize_module(mod)
    from hm import infer_types
    types, casts = infer_types(mod.roots)
    write_mod_repr('views/' + name + '.txt', mod, [types, casts])
    from mogrify import mogrify
    c = mogrify(mod, types)
    write_mod_repr('views/' + name + '.c.txt', c, [])
    from c import write_c
    write_c(c, 'views')
    serialize_module(c)
    return mod

def load_module(filename):
    deps = set()
    print 'Loading %s' % (filename,)
    mod = load_module_dep(filename, deps)
    print 'Loaded [%s] for %s' % (', '.join(d.name for d in deps), filename)
    return (mod, deps)

add_sym('length')
add_sym('deps')
add_sym('roots')
add_sym('type')
add_sym('instantiation')
map(add_sym, 'void,int,bool,char,str,tuple,func,typevar'.split(','))
add_sym('tuple*')
map(add_sym, ('None,True,False,getattr,ord,range,len,set,'
        '+,-,*,/,//,%,negate,==,!=,<,>,<=,>=,is,is not,in,not in,'
        'slice,printf,object').split(','))

def walk_atoms(atoms, f):
    for atom in atoms:
        f(atom)
        walk_atoms(atom.subs, f)

char_escapes = dict(zip('"\n\\\t\r\0\b\a\f\v', '"n\\tr0bafv'))

def escape_str(s):
    return '"%s"' % (''.join('\\' + char_escapes[c] if c in char_escapes
                             else c for c in s),)

SerializeInit = DT('SerializeInit', ('natoms', int),
                                    ('atomixs', {Atom: int}),
                                    ('modset', set([Module])),
                                    ('unknown_refatoms', set([Atom])))

def serialize_module(module):
    if module.digest:
        print '%s is already serialized' % (module.name,)
        return
    state = SerializeInit(0, {}, set(), set())
    def init_serialize(atom, state=state):
        assert hasattr(atom, 'subs'), "Expected atom, got: %s" % (atom,)
        state.atomixs[atom] = state.natoms
        state.natoms += 1
        r = match(atom, ('Ref(r, _)', identity), ('_', lambda: None))
        if r is not None:
            m = loaded_module_atoms.get(r)
            if m is not None:
                state.modset.add(m[1])
            else:
                state.unknown_refatoms.add(r)
    walk_atoms(module.roots, init_serialize)

    nmods = len(state.modset)
    base = 7 + nmods
    natoms = base + state.natoms
    selfixs = {}
    for atom, i in state.atomixs.iteritems():
        selfixs[atom] = (i + base + 1, module)
        if atom in state.unknown_refatoms:
            state.unknown_refatoms.remove(atom)
    assert not state.unknown_refatoms, ("A dependency of %s has not been "
            "serialized; %d atom(s) orphaned:\n%s") % (module.name,
            len(state.unknown_refatoms),
            '\n>'.join(repr(s) for s in state.unknown_refatoms))
    deps = ""
    modixs = {}
    for m, mod in enumerate(sorted(state.modset)):
        modixs[mod] = m + 1
        deps += escape_str(mod.digest) + "\n"
    nroots = len(module.roots)
    header = '"";4\n1;1\n%s\n2;1\n%d\n3%s\n%s4%s\n' % (
             escape_str(module.name), natoms, ";%d" % nmods if nmods else "",
             deps, ";%d" % nroots if nroots else "")
    hash = sha256(header)
    temp = '/tmp/serialize'
    f = file(temp, 'wb')
    f.write(header)
    def refstr(ra):
        s = selfixs.get(ra)
        if s is not None:
            return 's%d' % (s[0],)
        ix, mod = loaded_module_atoms[ra]
        return 'r%d %d' % (ix, modixs[mod])
    def output(str):
        hash.update(str)
        f.write(str)
    def serialize_atom(atom):
        match(atom, ("Int(i, _)", lambda i: output(str(i))),
                    ("Str(s, _)", lambda s: output(escape_str(s))),
                    ("Ref(r, _)", lambda r: output(refstr(r))))
        n = len(atom.subs)
        output(";%d\n" % n if n else "\n")
    walk_atoms(module.roots, serialize_atom)
    f.close()
    module.digest = hash.digest().encode('hex')
    system('mv -f -- %s mods/%s' % (temp, module.digest))
    system('ln -sf -- %s mods/%s' % (module.digest, module.name))
    loaded_module_atoms.update(selfixs)
    loaded_modules[module.name] = module

# FFFFUUUU
GLOBAL_OVERLAYS = []

def write_mod_repr(filename, m, overlays):
    global GLOBAL_OVERLAYS
    GLOBAL_OVERLAYS = overlays
    with file(filename, 'w') as f:
        for r in m.roots:
            f.write(repr(r))
    GLOBAL_OVERLAYS = []

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

@matcher('sym')
def _match_sym(atom, ast):
    assert 2 <= len(ast.args) <= 3
    mod_name = ast.args[0].value
    assert mod_name in loaded_modules, "%s not loaded" % mod_name
    mod = loaded_modules[mod_name]
    if isinstance(atom, Ref):
        r = atom.refAtom
        if isinstance(r, Ref) and r.refAtom is _b_symbol:
            for sub in r.subs:
                if getattr(sub, 'refAtom', None) is _b_name:
                    nm = sub.subs[0].strVal
                    break
            else:
                return None
            m = match_try(nm, ast.args[1])
            if m is None or len(ast.args) == 2:
                return m
            msubs = match_try(atom.subs, ast.args[2])
            if msubs is not None:
                return m + msubs
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
        if s.refAtom in boot_syms:
            label = s.refAtom.subs[0].subs[0].strVal
        elif s.refAtom in csym_roots:
            label = s.refAtom.subs[0].subs[0].strVal + '*'
        elif hasattr(s.refAtom, 'strVal'):
            label = '->%r' % (s.refAtom.strVal,)
        elif getattr(s.refAtom, 'subs', []):
            for sub in s.refAtom.subs:
                if getattr(sub, 'refAtom', None) is _b_name:
                    label = '->%s' % (sub.subs[0].strVal,)
                    if getattr(s.refAtom, 'refAtom', None) in boot_syms:
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
    global GLOBAL_OVERLAYS
    for overlay in GLOBAL_OVERLAYS:
        if s in overlay:
            r.append('  ' * (indent+1) + repr(overlay[s]))
    if hasattr(s, 'subs'):
        if not isinstance(s.subs, list):
            invalid = 'INVALID SUBS: ' + repr(s.subs)
            #print invalid
            r.append('  ' * (indent+1) + invalid)
        else:
            for sub in s.subs:
                _do_repr(sub, r, indent + 1)

def atom_repr(s):
    r = []
    _do_repr(s, r, 0)
    r.append('')
    return '\n'.join(r)

Int.__repr__ = Str.__repr__ = Ref.__repr__ = atom_repr

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
