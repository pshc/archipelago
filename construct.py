#!/usr/bin/env python2
from base import *
from globs import *
from bedrock import *
import types_builtin
import native
import atom
import astconv
import expand
import scan
import prop
import llvm

# TEMP
Entry = base.DT('Entry', ('key', '*a'), ('value', str))
Overlay = base.DT('Overlay', ('mapping', [Entry]))

def extrinsic_mod(extr, mapping, src_mod):
    items = {}
    for k, v in mapping.iteritems():
        if has_extrinsic(Location, k):
            loc = extrinsic(Location, k)
            if loc.module is src_mod:
                assert has_extrinsic(extr, k), "Un-extrinsiced value in map?!"
                assert loc.index not in items, "%r appears twice" % (v,)
                items[loc.index] = Entry(k, v)
    mod = Module(t_DT(Overlay), Overlay([items[k] for k in sorted(items)]))
    add_extrinsic(Name, mod, extrinsic(Name, src_mod) + '_' + extr.label)
    return mod

def load_module_dep(filename, deps):
    assert filename.endswith('.py')
    name = filename.replace('/', '_')[:-3]
    if name in loaded_modules:
        mod = loaded_modules[name]
        assert mod is not None, "%s is not ready yet!" % (name,)
        deps.add(mod)
        return mod
    loaded_modules[name] = None
    def conv_mod():
        names = {}
        mod = capture_extrinsic(Name, names,
            lambda: astconv.convert_file(filename, name, deps))
        atom.write_mod_repr('views/' + name + '.txt', mod, [Name])

        native.serialize(mod)
        names_mod = extrinsic_mod(Name, names, mod)
        native.serialize(names_mod)

        scan.scan_root(mod.root)
        atom.write_mod_repr('views/' + name + '.txt', mod,
                [Name, TypeOf, InstMap])
        prop.prop_types(mod.root)
        atom.write_mod_repr('views/' + name + '.txt', mod, [Name, TypeOf])

        return mod
    mod = scope_extrinsic(InstMap,
            lambda: scope_extrinsic(astconv.AstType,
            lambda: scope_extrinsic(astconv.AstHint, conv_mod)))

    return expand.in_expansion_env(lambda: _do_mod(mod, name))

def _do_mod(mod, name):
    expand.expand_module(mod)

    llvm.write_ir(mod.root)

    assert loaded_modules[name] is None
    loaded_modules[name] = mod
    return mod

def load_module(filename):
    deps = set()
    print 'Loading %s' % (filename,)
    mod = load_module_dep(filename, deps)
    dep_names = ', '.join(extrinsic(Name, d) for d in deps)
    print 'Loaded [%s] for %s' % (dep_names, filename)
    return (mod, deps)

def resolve_forward_type_refs():
    for dt in DATATYPES.itervalues():
        for ctor in dt.__form__.ctors:
            for f in ctor.fields:
                _resolve_walk(f.type, (f, 'type'))

def _resolve_walk(node, path):
    if isinstance(node, TForward):
        nm = node.name
        if nm == 'set':
            nm = 'Set'
        assert nm in DATATYPES, "Can't resolve forward type '%s'" % (nm,)
        form = DATATYPES[nm].__form__
        assert isinstance(form, DataType), "Bad form %s" % (form,)
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
        _resolve_walk(node.appTarget, (node, 'appTarget'))
        if isinstance(node.appVar, basestring):
            node.appVar = _resolve_tvar(node.appTarget, node.appVar)
        _resolve_walk(node.appArg, (node, 'appArg'))
    elif isinstance(node, TArray):
        _resolve_walk(node.elemType, (node, 'elemType'))
    elif isinstance(node, TWeak):
        _resolve_walk(node.refType, (node, 'refType'))

def _resolve_tvar(node, name):
    if isinstance(node, TData):
        for tvar in node.data.tvars:
            if extrinsic(Name, tvar) == name:
                return tvar
    elif isinstance(node, TApply):
        return _resolve_tvar(node.appTarget, name)
    assert False, "Couldn't find TVar named '%s'" % (name,)

BuiltinList = DT('BuiltinList', ('builtins', [atom.Builtin]))

def load_builtins():
    astconv.setup_builtin_module()
    root = BuiltinList(map(snd, sorted(atom.BUILTINS.items())))
    mod = Module(t_DT(BuiltinList), root)
    add_extrinsic(Name, mod, 'builtins')
    exports = {}
    for name, sym in atom.BUILTINS.iteritems():
        exports[name] = sym
    astconv.loaded_module_export_names[mod] = exports

    atom.write_mod_repr('views/symbols.txt', mod, [Name])

    native.serialize(mod)

def load_forms():
    resolve_forward_type_refs()

    pending = set([atom.CompilationUnit.__dt__.__form__])
    done = set()
    forms = []
    names = {}

    def found_dt(dt):
        if dt not in done:
            assert isinstance(dt, DataType), '%s is not a DT form' % (dt,)
            pending.add(dt)

    def found_tvar(tvar):
        names[tvar] = extrinsic(Name, tvar)

    def found_apply(d, a):
        scan_type_deps(d)
        scan_type_deps(a)

    def scan_type_deps(t):
        assert isinstance(t, Type), "%r is not a type" % (t,)
        match(t,
            ('TTuple(ts)', lambda ts: map(scan_type_deps, ts)),
            ('TFunc(a, r)', lambda a, r: map(scan_type_deps, a + [r])),
            ('TData(dt)', found_dt),
            ('TApply(d, _, a)', found_apply),
            ('TArray(e)', scan_type_deps),
            ('TWeak(t)', scan_type_deps),
            ('TVar(tvar)', found_tvar),
            ('_', lambda: None))

    while pending:
        dt = pending.pop()
        done.add(dt)
        if not has_extrinsic(Location, dt):
            for ctor in dt.ctors:
                for field in ctor.fields:
                    scan_type_deps(field.type)
                    names[field] = extrinsic(Name, field)
                names[ctor] = extrinsic(Name, ctor)
            forms.append(dt)
            names[dt] = extrinsic(Name, dt)

    mod = Module(t_DT(DtList), DtList(forms))
    add_extrinsic(Name, mod, 'forms')
    atom.write_mod_repr('views/forms.txt', mod, [Name])
    native.serialize(mod)

    names_mod = extrinsic_mod(Name, names, mod)
    native.serialize(names_mod)

DtList = DT('DtList', ('dts', [DataType]))

def load_files(files):
    load_builtins()
    load_forms()
    load_module('bedrock.py')
    for filename in files:
        load_module(filename)

def main():
    import sys
    files = []
    argv = sys.argv[1:]
    options = GenOpts(False, None, False)
    while argv:
        arg = argv.pop(0)
        if arg == '--':
            files += argv
            break
        elif arg.startswith('-'):
            if arg == '-q':
                options.quiet = True
            elif arg == '--color':
                from IPython.utils.coloransi import TermColors
                options.color = TermColors
            elif arg == '-t':
                options.dumpTypes = True
            else:
                assert False, "Unknown option: %s" % (arg,)
        else:
            files.append(arg)
    in_env(GENOPTS, options,
        lambda: scope_extrinsic(Location,
        lambda: scope_extrinsic(ModIndex,
        lambda: scope_extrinsic(ModDigest,
        lambda: scope_extrinsic(TypeOf,
        lambda: load_files(files)
    )))))

if __name__ == '__main__':
    main()

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
