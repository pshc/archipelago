#!/usr/bin/env python2
from base import *
from globs import *
from bedrock import *
import types_builtin
import native
import atom
import astconv
import check
import expand
import scan
import prop
import llvm

# TEMP
Entry = base.DT('Entry', ('key', '*a'), ('value', str))
Overlay = base.DT('Overlay', ('mapping', [Entry]))

Plan = DT('Plan', ('moduleName', str),
                  ('writeIR', 'Maybe(str)'),
                  ('linkBinary', 'Maybe(str)'))

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

def dep_obj_plan(filename):
    name = module_name_from_py(filename)
    return Plan(name, Just('ir/' + name + '.ll'), Nothing())

def module_name_from_py(src):
    assert src.endswith('.py')
    name = src.replace('/', '_')[:-3]
    if src.startswith('tests/'):
        name = name[6:]
    return name

def load_module_dep(src, deps, plan):
    name = plan.moduleName
    if name in loaded_modules:
        mod = loaded_modules[name]
        assert mod is not None, "%s is not ready yet!" % (name,)
        deps.add(mod)
        return mod
    loaded_modules[name] = None
    names = {}

    def conv_mod():
        mod = capture_extrinsic(Name, names,
            lambda: astconv.convert_file(src, name, deps))
        add_extrinsic(Filename, mod, name)

        view = 'views/%s' % (name,)
        atom.write_mod_repr(view, mod, [Name])

        scan.scan_root(mod.root)
        atom.write_mod_repr(view, mod, [Name, TypeOf, InstMap])

        prop.prop_types(mod.root)
        atom.write_mod_repr(view, mod, [Name, TypeOf, Instantiation])

        return mod
    mod = scope_extrinsic(InstMap,
            lambda: scope_extrinsic(astconv.AstType,
            lambda: scope_extrinsic(astconv.AstHint, conv_mod)))

    native.serialize(mod)
    names_mod = extrinsic_mod(Name, names, mod)
    native.serialize(names_mod)

    return expand.in_intramodule_env(
        lambda: check.in_check_env(
        lambda: _do_mod(mod, plan)
    ))

def _do_mod(mod, plan):
    casts = check.check_types(mod.root)

    expand.expand_module(mod)

    name = extrinsic(Filename, mod)

    compiled = False
    if isJust(plan.writeIR):
        llvm.write_ir(mod, fromJust(plan.writeIR))
        compiled = llvm.compile(mod)

    if isJust(plan.linkBinary):
        binFilename = fromJust(plan.linkBinary)
        import os
        try:
            os.unlink(binFilename)
        except OSError:
            pass
        if compiled:
            if llvm.link(mod, binFilename):
                print col('Green', 'Linked'), name

    assert loaded_modules[name] is None
    loaded_modules[name] = mod
    return mod

def load_module(filename):
    print col('DG', 'Loading'), filename

    plan = dep_obj_plan(filename)
    if filename.startswith('tests/'):
        plan.linkBinary = Just('bin/' + plan.moduleName)

    deps = set()
    mod = load_module_dep(filename, deps, plan)
    return (mod, deps)

def resolve_forward_type_refs():
    for dt in DATATYPES.itervalues():
        for ctor in extrinsic(FormSpec, dt).ctors:
            for f in ctor.fields:
                _resolve_walk(f.type, (f, 'type'))

def _resolve_walk(node, path):
    if isinstance(node, TForward):
        nm = node.name
        if nm == 'set':
            nm = 'Set'
        assert nm in DATATYPES, "Can't resolve forward type '%s'" % (nm,)
        form = extrinsic(FormSpec, DATATYPES[nm])
        assert isinstance(form, DataType), "Bad form %s" % (form,)
        dest = vanilla_tdata(form)

        # Also restore any types applied to this TForward
        for i, appT in enumerate(node.appTypes):
            dest.appTypes[i] = appT
            _resolve_walk(appT, (dest.appTypes, i))

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
    elif isinstance(node, TData):
        for i, t in enumerate(node.appTypes):
            _resolve_walk(t, (node.appTypes, i))
    elif isinstance(node, TArray):
        _resolve_walk(node.elemType, (node, 'elemType'))
    elif isinstance(node, TWeak):
        _resolve_walk(node.refType, (node, 'refType'))

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

    atom.write_mod_repr('views/symbols', mod, [Name])

    native.serialize(mod)

def load_forms():
    resolve_forward_type_refs()

    pending = set([extrinsic(FormSpec, atom.CompilationUnit.__dt__)])
    done = set()
    forms = []
    names = {}

    def found_dt(dt, apps):
        if dt not in done:
            assert isinstance(dt, DataType), '%s is not a DT form' % (dt,)
            pending.add(dt)
        map_(scan_type_deps, apps)

    def found_tvar(tvar):
        names[tvar] = extrinsic(Name, tvar)

    def scan_type_deps(t):
        assert isinstance(t, Type), "%r is not a type" % (t,)
        match(t,
            ('TTuple(ts)', lambda ts: map(scan_type_deps, ts)),
            ('TFunc(a, r)', lambda a, r: map(scan_type_deps, a + [r])),
            ('TData(dt, apps)', found_dt),
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
    atom.write_mod_repr('views/forms', mod, [Name])
    native.serialize(mod)

    names_mod = extrinsic_mod(Name, names, mod)
    native.serialize(names_mod)

DtList = DT('DtList', ('dts', [DataType]))

def load_files(files):
    load_builtins()
    load_forms()
    load_module('runtime.py')
    load_module('bedrock.py')
    for filename in files:
        load_module(filename)

def in_construct_env(func):
    extrs = [Filename, Location,
            ModIndex, ModDigest, ModDeps,
            TypeOf, TypeVars, Instantiation]
    return capture_scoped(extrs, {}, func)

def main():
    import sys
    files = []
    argv = sys.argv[1:]
    options = GenOpts(False, None, False, False)
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
            elif arg == '-i':
                options.dumpInsts = True
            else:
                assert False, "Unknown option: %s" % (arg,)
        else:
            files.append(arg)
    in_env(GENOPTS, options,
            lambda: in_construct_env(
            lambda: expand.in_intermodule_env(
            lambda: llvm.in_llvm_env(
            lambda: load_files(files)))))

if __name__ == '__main__':
    main()

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
