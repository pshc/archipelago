#!/usr/bin/python2
from os import system
from hashlib import sha256
from base import *
from types_builtin import *
from bedrock import *
from globs import loaded_modules, loaded_module_atoms

Builtin = DT('Builtin')

Field = DT('Field', ('type', Type))

Ctor = DT('Ctor', ('fields', [Field]))

Ctxt = DT('Ctxt', ('type', Type))

Extrinsic = DT('Extrinsic', ('type', Type))

Var = DT('Var')

Binding, BindBuiltin, BindCtor, BindDT, BindField, BindFunc, BindVar = \
    ADT('Binding',
        'BindBuiltin', ('builtin', '*Builtin'),
        'BindCtor', ('ctor', '*Ctor'),
        'BindDT', ('dtStmt', '*DTStmt'),
        'BindField', ('field', '*Field'),
        'BindFunc', ('func', '*Func'),
        'BindVar', ('var', '*Var'))

Pat, PatCtor, PatCapture, PatInt, PatStr, PatTuple, PatVar, PatWild = \
    ADT('Pat',
        'PatCtor', ('ctor', '*Ctor'), ('args', '[Pat]'),
        'PatCapture', ('var', Var), ('pattern', 'Pat'),
        'PatInt', ('val', int),
        'PatStr', ('val', str),
        'PatTuple', ('vals', '[Pat]'),
        'PatVar', ('var', Var),
        'PatWild')

MatchCase = DT('MatchCase', ('pat', Pat), ('result', 'Expr'))

Expr, And, Attr, Bind, Call, DictLit, GenExpr, GetCtxt, InCtxt, IntLit, \
        Lambda, ListLit, Match, Or, StrLit, Ternary, TupleLit = \
    ADT('Expr',
        'And', ('left', 'Expr'), ('right', 'Expr'),
        'Attr', ('expr', 'Expr'), ('field', '*Field'),
        'Bind', ('binding', 'Binding'),
        'Call', ('func', 'Expr'), ('args', '[Expr]'),
        'DictLit', ('vals', '[(Expr, Expr)]'),
        'GenExpr', ('expr', 'Expr'), ('pattern', 'Pat'),
                   ('listExpr', 'Expr'), ('preds', '[Expr]'),
        'GetCtxt', ('ctxt', '*Ctxt'),
        'InCtxt', ('ctxt', '*Ctxt'), ('init', 'Expr'), ('expr', 'Expr'),
        'IntLit', ('val', int),
        'Lambda', ('params', [Var]), ('expr', 'Expr'),
        'ListLit', ('vals', '[Expr]'),
        'Match', ('expr', 'Expr'), ('cases', [MatchCase]),
        'Or', ('left', 'Expr'), ('right', 'Expr'),
        'StrLit', ('val', str),
        'Ternary', ('test', 'Expr'), ('then', 'Expr'), ('else_', 'Expr'),
        'TupleLit', ('vals', '[Expr]'))

AugOp, AugAdd, AugSubtract, AugMultiply, AugDivide, AugModulo = ADT('AugOp',
        'AugAdd', 'AugSubtract', 'AugMultiply', 'AugDivide', 'AugModulo')

Body = DT('Body', ('stmts', '[Stmt]'))

CondCase = DT('CondCase', ('test', Expr), ('body', Body))

Func = DT('Func', ('params', [Var]), ('body', Body))

Lhs, LhsVar, LhsAttr, LhsTuple = ADT('Lhs',
        'LhsVar', ('var', '*Var'),
        'LhsAttr', ('sub', 'Lhs'), ('attr', '*Field'),
        'LhsTuple', ('vals', '[Lhs]'))

Stmt, Assert, Assign, AugAssign, Break, Cond, Continue, CtxtStmt, Defn, \
    DTStmt, ExprStmt, ExtrinsicStmt, FuncStmt, Return, ReturnNothing, While = \
    ADT('Stmt',
        'Assert', ('test', Expr), ('message', Expr),
        'Assign', ('lhs', Lhs), ('expr', Expr),
        'AugAssign', ('op', AugOp), ('lhs', Lhs), ('expr', Expr),
        'Break',
        'Cond', ('cases', [CondCase]), ('elseCase', 'Maybe(Body)'),
        'Continue',
        'CtxtStmt', ('ctxt', Ctxt),
        'Defn', ('var', 'Var'), ('expr', Expr),
        'DTStmt', ('ctors', [Ctor]), ('tvars', ['TypeVar']),
        'ExprStmt', ('expr', Expr),
        'ExtrinsicStmt', ('extrinsic', Extrinsic),
        'FuncStmt', ('func', Func),
        'Return', ('expr', Expr),
        'ReturnNothing',
        'While', ('test', Expr), ('body', Body))

# Bootstrap module
boot_syms = []
boot_sym_names = {}

csym_roots = []

def symref(name):
    assert name in boot_sym_names, '%s not a boot symbol' % (name,)
    return boot_sym_names[name]

def getident(ref):
    return match(ref, ('Ref(named(nm), _)', identity))

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
        t = TFunc_(t[:-1], t[-1])
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

def add_sym(name):
    node = boot_sym_names.get(name)
    if not node:
        """
        subs = [Ref(_b_name, [Str(name, [])])]
        t = builtin_type_to_atoms(name)
        if t is not None:
            subs.append(t)
        """
        node = Builtin()
        add_extrinsic(Name, node, name)
        boot_syms.append(node)
        boot_sym_names[name] = node
    return node

def load_module_dep(filename, deps):
    assert filename.endswith('.py')
    name = filename.replace('/', '_')[:-3]
    if name in loaded_modules:
        mod = loaded_modules[name]
        deps.add(mod)
        return mod
    from ast import convert_file
    mod = convert_file(filename, name, deps)
    write_mod_repr('views/' + name + '.txt', mod, {})
    serialize_module(mod)
    from hm import infer_types
    overlays = infer_types(mod.roots)
    write_mod_repr('views/' + name + '.txt', mod, overlays)
    from expand import expand_ast
    overlays.update(expand_ast(mod.roots))
    write_mod_repr('views/' + name + '.txt', mod, overlays)
    from mogrify import mogrify
    c = mogrify(mod, overlays)
    write_mod_repr('views/' + name + '.c.txt', c, {})
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
add_sym('type')
add_sym('xref')
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
                                    ('atomixs', {object: int}),
                                    ('modset', set([Module])),
                                    ('unknown_refatoms', set([object])))

def serialize_module(module):
    if module.digest:
        print '%s is already serialized' % (module.name,)
        return
    state = SerializeInit(0, {}, set(), set())
    def init_serialize(atom, state=state):
        if hasattr(type(atom), '__types__'):
            print type(atom).__types__
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

# Everything went better than expected
GLOBAL_OVERLAYS = {}

def write_mod_repr(filename, m, overlays):
    global GLOBAL_OVERLAYS
    GLOBAL_OVERLAYS = overlays
    with file(filename, 'w') as f:
        for r in m.roots:
            f.write(repr(r))
    GLOBAL_OVERLAYS = {}

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
    assert len(ast.args) == 1
    name = ast.args[0].value
    target = boot_sym_names.get(name)
    return [] if atom is target else None

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
            if label == 'xref':
                r.append('  ' * indent + 'xref:')
                _do_repr(s.subs[0].refAtom, r, indent+1)
                return
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
    for info, overlay in GLOBAL_OVERLAYS.iteritems():
        if s in overlay:
            r.append('  ' * indent + info.annotate(overlay[s]))
    if hasattr(s, 'subs'):
        if not isinstance(s.subs, list):
            invalid = 'INVALID SUBS: ' + repr(s.subs)
            #print invalid
            r.append('  ' * (indent+1) + invalid)
        else:
            for sub in s.subs:
                _do_repr(sub, r, indent + 1)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
