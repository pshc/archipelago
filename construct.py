#!/usr/bin/env python2
from base import *
from globs import *
from bedrock import *
from maybe import *
import types_builtin
import native
import deserialize
import atom
import vat
import astconv
import check
import quilt
import pltfm
import expand
import headers
import scan
import prop
import llvm

import os.path

BuildOpts = DT('BuildOpts', ('outDir', str),
                            ('writeHeaders', bool),
                            ('buildTests', bool))

BUILDOPTS = new_env('BUILDOPTS', BuildOpts)

# ought to be just a dict
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
    name = llvm.module_name_from_py(filename)
    ll = os.path.join(env(BUILDOPTS).outDir, name + '.ll')
    return Plan(name, Just(ll), Nothing())

def load_module_dep(src, deps, plan):
    name = plan.moduleName
    if name in WRITTEN_MODULES:
        mod = WRITTEN_MODULES[name]
        assert mod is not None, "%s is not ready yet!" % (name,)
        deps.add(mod)
        return mod
    WRITTEN_MODULES[name] = None
    names = {}

    def conv_mod():
        checkpoint()
        bundle_mod = capture_extrinsic(Name, names,
            lambda: astconv.convert_file(src, name, deps))
        decl_mod = bundle_mod.root.decls[0]
        add_extrinsic(Filename, decl_mod, name)
        view = 'views/%s' % (name,)
        if len(bundle_mod.root.units) == 0:
            atom.write_mod_repr(view, decl_mod)
            prop.prop_module_decls(decl_mod.root)
            atom.write_mod_repr(view, decl_mod, [TypeOf])
            return bundle_mod
        profile_separator()

        defn_mod = bundle_mod.root.units[0]

        impv = view
        view += '_decls'
        atom.write_mod_repr(view, decl_mod)
        atom.write_mod_repr(impv, defn_mod)

        scan.scan_unit(defn_mod.root)

        prop.prop_module_decls(decl_mod.root)
        atom.write_mod_repr(view, decl_mod, [TypeOf])
        checkpoint('module conversion and setup')
        prop.prop_compilation_unit(defn_mod.root)
        checkpoint('propped defns')
        atom.write_mod_repr(impv, defn_mod, [TypeOf, Instantiation])
        checkpoint()

        return bundle_mod
    bundle_mod = scope_extrinsic(InstMap,
            lambda: scope_extrinsic(astconv.AstType,
            lambda: scope_extrinsic(astconv.AstHint, conv_mod)))
    bundle = bundle_mod.root

    checkpoint()
    for decl_mod in bundle.decls:
        native.serialize(decl_mod)
        names_mod = extrinsic_mod(Name, names, decl_mod)
        native.serialize(names_mod)
        bundle.overlays.append(names_mod)

    if len(bundle.units) > 0:
        for mod in bundle.units:
            native.serialize(mod)
            names_mod = extrinsic_mod(Name, names, mod)
            native.serialize(names_mod)
            bundle.overlays.append(names_mod)
        checkpoint('serialized decls and defns')

        native.serialize(bundle_mod)

        def build():
            # really should link unit to its decl mod
            for decl_mod, defn_mod in ezip(bundle.decls, bundle.units):
                build_mod(decl_mod, defn_mod, plan)
        expand.in_intramodule_env(lambda: check.in_check_env(build))
    else:
        native.serialize(bundle_mod)
        checkpoint('serialized just decls')
        for decl_mod in bundle.decls:
            expand.expand_decls(decl_mod.root)
        checkpoint('expanded decls')
        if isJust(plan.writeIR):
            for decl_mod in bundle.decls:
                write_mod_headers(decl_mod, fromJust(plan.writeIR))

    assert WRITTEN_MODULES[name] is None
    WRITTEN_MODULES[name] = bundle_mod

    if name == 'maybe':
        # Stupid hack
        # expanded forms depend on maybe, but maybe depends on type forms
        # so just load the xforms now
        load_forms('xforms', [quilt.BlockUnit])

    return bundle_mod

def build_mod(decl_mod, defn_mod, plan):
    name = extrinsic(Filename, decl_mod)
    impv = 'views/%s' % (name,)
    view = '%s_xdecls' % (impv,)

    checkpoint()
    casts = check.check_types(decl_mod, defn_mod)
    checkpoint('checked types')
    atom.write_mod_repr(impv, defn_mod, [TypeOf, TypeCast])

    checkpoint()
    new_decls, flat_unit = sub_profile('expanding module',
            lambda: expand.expand_module(decl_mod, defn_mod))
    xdecl_mod = Module(t_DT(atom.ModuleDecls), new_decls)
    defn_mod = Module(t_DT(quilt.BlockUnit), flat_unit)
    add_extrinsic(Name, xdecl_mod, '%sX' % (name,))
    add_extrinsic(Name, defn_mod, name)
    atom.write_mod_repr(view, xdecl_mod, [TypeOf])
    atom.write_mod_repr(impv+'_x', defn_mod, [quilt.LLVMTypeOf, TypeCast])
    checkpoint()
    native.serialize(xdecl_mod)
    native.serialize(defn_mod)
    checkpoint('serialized expanded module')

    llvm.compute_link_deps(decl_mod, xdecl_mod, defn_mod)

    compiled = False
    if isJust(plan.writeIR):
        ir = fromJust(plan.writeIR)
        checkpoint()
        llvm.write_ir(decl_mod, xdecl_mod, defn_mod, ir)
        checkpoint('wrote ir')
        compiled = llvm.compile(decl_mod)
        write_mod_headers(decl_mod, ir)

    if isJust(plan.linkBinary):
        binFilename = fromJust(plan.linkBinary)
        import os
        try:
            os.unlink(binFilename)
        except OSError:
            pass
        if compiled:
            if llvm.link(decl_mod, binFilename):
                print col('Green', 'Linked'), name

def write_mod_headers(mod, ir):
    if env(BUILDOPTS).writeHeaders:
        hdr = ir[:-3].replace('obj', 'include') + '.h'
        sym = extrinsic(Filename, mod)
        headers.write_export_header(mod, hdr, sym)

astconv.load_module = lambda nm, ds: load_module_dep(nm, ds, dep_obj_plan(nm))

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

        # Hack for Ret(_)
        if len(path) == 3:
            node, first, second = path
            path = getattr(node, first), second

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
        for i, arg in enumerate(node.paramTypes):
            _resolve_walk(arg, (node.paramTypes, i))
        if matches(node.result, 'Ret(_)'):
            _resolve_walk(node.result.type, (node, 'result', 'type'))
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

    atom.write_mod_repr('views/symbols', mod)

    native.serialize(mod)

SERIALIZED_FORMS = set()

def load_forms(modName, init):
    resolve_forward_type_refs()

    pending = set(t_DT(dt).data for dt in init)
    forms = []
    names = {}

    def found_dt(dt, apps):
        if dt not in SERIALIZED_FORMS:
            assert isinstance(dt, DataType), '%s is not a DT form' % (dt,)
            pending.add(dt)
        map_(scan_type_deps, apps)

    def found_tvar(tvar):
        names[tvar] = extrinsic(Name, tvar)

    def scan_type_deps(t):
        assert isinstance(t, Type), "%r is not a type" % (t,)
        match(t,
            ('TTuple(ts)', lambda ts: map_(scan_type_deps, ts)),
            ('TFunc(a, Ret(r), _)', lambda a, r: map_(scan_type_deps, a+[r])),
            ('TFunc(a, _, _)', lambda a: map_(scan_type_deps, a)),
            ('TData(dt, apps)', found_dt),
            ('TArray(e, _)', scan_type_deps),
            ('TWeak(t)', scan_type_deps),
            ('TVar(tvar)', found_tvar),
            ('TPrim(_)', nop))

    while pending:
        dt = pending.pop()
        SERIALIZED_FORMS.add(dt)
        if not has_extrinsic(Location, dt):
            for ctor in dt.ctors:
                for field in ctor.fields:
                    scan_type_deps(field.type)
                    names[field] = extrinsic(Name, field)
                names[ctor] = extrinsic(Name, ctor)
            forms.append(dt)
            names[dt] = extrinsic(Name, dt)

    mod = Module(t_DT(DtList), DtList(forms))
    add_extrinsic(Name, mod, modName)
    atom.write_mod_repr('views/%s' % (modName,), mod)
    native.serialize(mod)

    names_mod = extrinsic_mod(Name, names, mod)
    native.serialize(names_mod)

    if modName == 'forms':
        deserialize.save_form_meanings(forms)

def load_runtime_dep(filename, subdeps):
    dep = load_module_dep(filename, set(), dep_obj_plan(filename))
    for decls in dep.root.decls:
        add_extrinsic(llvm.OFile, decls, RUNTIME_MODULE_OBJS[filename])
        add_extrinsic(llvm.LinkDeps, decls, frozenset(subdeps))
    return dep

def load_files(files):
    load_forms('forms', [
        atom.Bundle, atom.ModuleDecls, atom.CompilationUnit,
        Overlay, BuiltinList,
        atom.Vector,
    ])
    load_builtins()

    buildTests = env(BUILDOPTS).buildTests

    print col('DG', 'Building for ' + env(quilt.ARCH).name)
    runtime_mod = load_runtime_dep('runtime.py', [])
    load_runtime_dep('gc/interface.py', [runtime_mod.root.decls[0]])

    for filename in files:
        print col('DG', 'Loading'), filename
        plan = dep_obj_plan(filename)
        if buildTests:
            plan.linkBinary = Just(os.path.join('bin/', plan.moduleName))
        load_module_dep(filename, set(), plan)

def in_construct_env(func):
    extrs = [Filename,
            ModIndex, ModDigest, ModDeps,
            TypeVars, Instantiation]
    return capture_scoped(extrs, {}, func)

def main():
    import sys
    files = []
    argv = sys.argv[1:]
    genOpts = default_gen_opts()
    arch = None
    options = BuildOpts('ir/', False, False)
    while argv:
        arg = argv.pop(0)
        if arg == '--':
            files += argv
            break
        elif arg.startswith('-'):
            # General options
            if arg == '--color':
                from IPython.utils.coloransi import TermColors
                genOpts.color = TermColors
            elif arg == '--profile':
                genOpts.profile = True
            elif arg == '--views':
                genOpts.dumpViews = True
            elif arg == '--source':
                genOpts.dumpSource = True
            elif arg == '--types':
                genOpts.dumpTypes = True
            elif arg == '--insts':
                genOpts.dumpInsts = True
            elif arg == '--blocks':
                genOpts.dumpBlocks = True
            # Build options
            elif arg == '--c-header':
                options.writeHeaders = True
            elif arg == '-o':
                options.outDir = argv.pop(0)
            elif arg == '--test':
                options.buildTests = True
            elif arg == '--arm':
                arch = pltfm.arm_iOS_target()
            elif arg == '--i386':
                arch = pltfm.i386_iOS_target()
            else:
                assert False, "Unknown option: %s" % (arg,)
        else:
            files.append(arg)

    if arch is None:
        arch = pltfm.host_arch()

    in_env(GENOPTS, genOpts,
            lambda: in_env(BUILDOPTS, options,
            lambda: in_env(quilt.ARCH, arch,
            lambda: in_construct_env(
            lambda: expand.in_intermodule_env(
            lambda: load_files(files))))))

if __name__ == '__main__':
    main()

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
