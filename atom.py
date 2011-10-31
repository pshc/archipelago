#!/usr/bin/python2
from os import system
from hashlib import sha256
from base import *
from bedrock import *
from globs import *
from types_builtin import *

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
        'BindDT', ('form', '*DtForm'), # XXX
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

Expr, And, Attr, Bind, Call, DictLit, GenExpr, GetCtxt, GetExtrinsic, \
        InCtxt, IntLit, \
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
        'GetExtrinsic', ('extrinsic', '*Extrinsic'), ('node', 'Expr'),
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
        'DTStmt', ('form', 'DtForm'),
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
    write_mod_repr('views/' + name + '.txt', mod, [Name])

    import native
    native.serialize(mod)

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
    native.serialize(c)
    return mod

def load_module(filename):
    deps = set()
    print 'Loading %s' % (filename,)
    mod = load_module_dep(filename, deps)
    print 'Loaded [%s] for %s' % (', '.join(d.name for d in deps), filename)
    return (mod, deps)

def resolve_forward_type_refs():
    for dt in DATATYPES.itervalues():
        for ctor in dt.__form__.ctors:
            for f in ctor.fields:
                _resolve_walk(f.type, (f, 'type'))

def _resolve_walk(node, path):
    if isinstance(node, TForward):
        nm = node.name
        assert nm in DATATYPES, "Can't resolve forward type '%s'" % (nm,)
        form = DATATYPES[nm].__form__
        assert isinstance(form, DtForm), "Bad form %s" % (form,)
        dest = TData(form)
        # Assign using path
        assert len(path) == 2
        node, last = path
        if isinstance(last, int):
            node[last] = dest
        elif isinstance(last, str):
            setattr(node, last, dest)
        else:
            assert False
    elif isinstance(node, TTuple):
        for i, t in enumerate(node.tupleTypes):
            _resolve_walk(t, (node.tupleTypes, i))
    elif isinstance(node, TFunc):
        for i, arg in enumerate(node.funcArgs):
            _resolve_walk(arg, (node.funcArgs, i))
        _resolve_walk(node.funcRet, (node, 'funcRet'))
    elif isinstance(node, TApply):
        _resolve_walk(node.appType, (node, 'appType'))
        for i, v in enumerate(node.appVars):
            _resolve_walk(v, (node.appVars, i))
    elif isinstance(node, TWeak):
        _resolve_walk(node.refType, (node, 'refType'))

BuiltinList = DT('BuiltinList', ('builtins', [Builtin]))

def load_builtins():
    root = BuiltinList(boot_syms)
    mod = Module('builtins', Nothing(), root)
    exports = {}
    for sym in boot_syms:
        exports[extrinsic(Name, sym)] = sym
    from ast import loaded_module_export_names
    loaded_module_export_names[mod] = exports

    write_mod_repr('views/symbols.txt', mod, [Name])

    import native
    native.serialize(mod)

def load_forms():
    resolve_forward_type_refs()

    pending = set([Body.__dt__.__form__])
    done = set()
    forms = []

    def found_dt(dt):
        if dt not in done:
            assert isinstance(dt, DtForm), '%s is not a DT form' % (dt,)
            pending.add(dt)

    def scan_type_deps(t):
        assert isinstance(t, Type), "%r is not a type" % (t,)
        match(t,
            ('TTuple(ts)', lambda ts: map(scan_type_deps, ts)),
            ('TFunc(a, r)', lambda a, r: map(scan_type_deps, a + [r])),
            ('TData(dt)', found_dt),
            ('TApply(a, vs)', lambda a, vs: map(scan_type_deps, [a] + vs)),
            ('TWeak(t)', scan_type_deps),
            ('_', lambda: None))

    while pending:
        dt = pending.pop()
        done.add(dt)
        for ctor in dt.ctors:
            for field in ctor.fields:
                scan_type_deps(field.type)
        forms.append(dt)

    mod = Module('forms', Nothing(), DtList(forms))
    write_mod_repr('views/forms.txt', mod, [Name])
    import native
    native.serialize(mod)

DtList = DT('DtList', ('dts', [DtForm]))

map(add_sym, ('None,True,False,getattr,ord,range,len,set,'
        '+,-,*,/,//,%,negate,==,!=,<,>,<=,>=,is,is not,in,not in,'
        'slice,printf,object').split(','))

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
    assert len(ast.args) == 1
    if has_extrinsic(Name, atom):
        return match_try(extrinsic(Name, atom), ast.args[0])
    return None

ModRepr = DT('ModRepr', ('write', 'str -> void'),
                        ('indent', int),
                        ('exts', [object]),
                        ('seen', set([object])),
                        ('weakIndices', {object: int}),
                        ('weakCtr', int))
MODREPR = new_context('MODREPR', ModRepr)

def write_mod_repr(filename, m, exts):
    with file(filename, 'w') as f:
        def write(x):
            f.write('%s%s\n' % ('  ' * context(MODREPR).indent, x))
        init = ModRepr(write, 0, exts, set(), {}, 0)
        in_context(MODREPR, init, lambda: _do_repr(m.root))

def _do_repr(s):
    c = context(MODREPR)
    if isinstance(s, DataType):
        dt = type(s)
        if s in c.seen:
            if s in c.weakIndices:
                c.write('<cyclic #%d>' % c.weakIndices[s])
            else:
                c.write('<cyclic %s 0x%x>' % (dt.__name__, id(s)))
            return
        c.seen.add(s)
        name = dt.__name__
        brief = pretty_brief(name, s)
        if brief and name != 'TupleLit':
            c.write(brief)
            return
        if s in c.weakIndices:
            name = '%s #%d' % (name, c.weakIndices[s])
        for ext in c.exts:
            if has_extrinsic(ext, s):
                name = '%s %s' % (name, extrinsic(ext, s))
        c.write(name)
        c.indent += 1
        form = dt.__form__
        assert not isinstance(form, DtForm)
        for field in form.fields:
            f = getattr(s, extrinsic(Name, field))
            p = match(field.type, ("TWeak(p)", Just), ("_", Nothing))
            if isJust(p):
                if isinstance(f, DataType):
                    if has_extrinsic(Name, f):
                        c.write('->%s' % (extrinsic(Name, f),))
                    else:
                        if f not in c.weakIndices:
                            c.weakCtr += 1
                            c.weakIndices[f] = c.weakCtr
                        c.write('->#%d %r' % (c.weakIndices[f], f))
                else:
                    c.write('->?? %r' % (f,))
            else:
                _do_repr(f)
        c.indent -= 1
    elif isinstance(s, (tuple, list)):
        l, r = '()' if isinstance(s, tuple) else '[]'
        if not s:
            c.write(l + r)
        else:
            c.write(l)
            for o in s:
                _do_repr(o)
            c.write(r)
    elif isinstance(s, value_types):
        c.write(repr(s))
    else:
        assert False, "Can't deal with %r" % (s,)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
