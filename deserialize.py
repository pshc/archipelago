from base import *
from bedrock import *
from globs import *
from hashlib import sha256
from native import ModuleMeta, HEADERS, DIGEST_INDEX
from types_builtin import app_map, subst
import os

LOADED_MODULES = {}

DeserialState = DT('DeserialState',
        ('file', file),
        ('module', Module),
        ('deps', {int: Module}),
        ('index', int),
        ('depsSeen', int),
        ('ownMap', {int: object}),
        ('forwardRefs', {int: [object]}))

Deserialize = new_env('Deserialize', DeserialState)

def _read_int(f):
    a = ord(f.read(1))
    if a <= 0b01111111:
        return a
    elif a <= 0b10111111:
        b = ord(f.read(1))
        a = ((a & 0b00111111)<<8) | b
        return a + 0x80
    elif a <= 0b11011111:
        b, c = map(ord, f.read(2))
        a = ((a & 0b00011111)<<16) | (b<<8) | c
        return a + 0x4080
    elif a <= 0b11101111:
        b, c, d = map(ord, f.read(3))
        a = ((a & 0b00001111)<<24) | (b<<16) | (c<<8) | d
        return a + 0x204080
    elif a == 0b11110000:
        b, c, d, e = map(ord, f.read(4))
        a = (b<<24) | (c<<16) | (d<<8) | e
        a += 0x10204080
        assert a < 0x100000000, "Int overflow"
        return a
    else:
        assert False, "Int overflow"

def read_int():
    return _read_int(env(Deserialize).file)

def read_bool():
    n = read_int()
    assert n == 0 or n == 1, "Bad bool: %d" % (n,)
    return bool(n)

def read_float():
    return read_int()

def read_str():
    n = read_int()
    return env(Deserialize).file.read(n).decode('UTF-8')

def read_node(t, path):
    if isinstance(t, TData):
        state = env(Deserialize)

        assert type(t.data) is DataType, "Bad TData containing %r" % (t.data,)
        apps = app_map(t.data, t.appTypes)

        ctors = t.data.ctors
        if len(ctors) > 1:
            form = ctors[read_int()]
        else:
            form = ctors[0]
        assert isinstance(form, Ctor), "Unexpected form %s" % (form,)
        ctor = extrinsic(TrueRepresentation, form)

        # Bleh.
        val = ctor(*[None for f in form.fields])
        if not t.data.opts.valueType:
            state.index += 1
            state.ownMap[state.index] = val
            add_extrinsic(Location, val, Pos(state.module, state.index))

        for field in form.fields:
            fnm = extrinsic(Name, field)
            ft = subst(apps, field.type)
            child = read_node(ft, (val, fnm))
            setattr(val, fnm, child)

        return val
    elif isinstance(t, TPrim):
        return match(t.primType, ("PInt()", read_int),
                                 ("PFloat()", read_float),
                                 ("PStr()", read_str),
                                 ("PBool()", read_bool))
    elif isinstance(t, TWeak):
        state = env(Deserialize)
        depIndex = read_int()
        if depIndex == 0:
            index = read_int()
            if index == 0:
                return state.module
            elif index in state.ownMap:
                return state.ownMap[index]
            else:
                # Resolve later
                state.forwardRefs.setdefault(index, []).append(path)
                return 'forward ref'
        else:
            if depIndex > state.depsSeen:
                assert depIndex == state.depsSeen+1, "skipped a dep?!"
                depHash = state.file.read(64)
                assert depHash == extrinsic(ModDigest, state.deps[depIndex-1])
                state.depsSeen += 1
            depMod = state.deps[depIndex-1]
            index = read_int()
            if index == 0:
                return depMod
            else:
                dest = extrinsic(ModIndex, depMod)[index-1]
                return dest

    elif isinstance(t, TArray):
        elemT = t.elemType
        n = read_int()
        elems = []
        for i in xrange(n):
            elems.append(read_node(elemT, (elems, i)))
        return elems
    else:
        assert False, "%r is not a type" % (t,)

def read_meta(filename):
    assert filename[:5] == 'mods/'
    f = file('cache/%s' % (filename[5:],), 'rb')
    atom_count = _read_int(f)
    dep_count = _read_int(f)
    deps = []
    for i in xrange(dep_count):
        hash_len = _read_int(f)
        assert hash_len == 64, "Weird hash length?!"
        deps.append(f.read(hash_len))
    f.close()
    return ModuleMeta(atom_count, deps)

def _read_module(filename):
    meta = read_meta(filename)

    deps = []
    for h in meta.deps:
        dep = LOADED_MODULES.get(h)
        if dep is None:
            dep = deserialize(h)
        deps.append(dep)

    f = file(filename, 'rb')
    module = Module(None, None)
    ownMap = {}
    forwardRefs = {}
    def go():
        header = f.read(4)
        if header == HEADERS['form']:
            module.rootType = t_DT(DtList)
        elif header == HEADERS['normal']:
            t = read_node(t_ADT(Type), (module, 'rootType'))
            assert type(match(t, 'TData(data, _)')) is DataType, \
                    "Bad TData containing %s: %r" % (type(t.data), t.data,)
            module.rootType = t
        else:
            assert False, "Bad module header: %s" % (header,)

        module.root = read_node(module.rootType, (module, 'root'))
        for index, paths in forwardRefs.iteritems():
            dest = ownMap[index]
            # resolve & replace each
            for path in paths:
                assert len(path) > 1, 'Path is too short'
                src = path[0]
                for step in path[1:-1]:
                    if isinstance(step, basestring):
                        src = getattr(src, step)
                    elif isinstance(step, int):
                        src = src[step]
                    else:
                        assert False, 'Bad path component'
                end = path[-1]
                if isinstance(end, basestring):
                    assert getattr(src, end) == 'forward ref'
                    setattr(src, end, dest)
                elif isinstance(end, int):
                    assert src[end] == 'forward ref'
                    src[end] = dest
                else:
                    assert False, 'Bad path end'
        return module
    state = DeserialState(f, module, deps, 0, 0, ownMap, forwardRefs)
    in_env(Deserialize, state, go)
    f.close()

    assert state.index == meta.count, "Inconsistent atom count"

    # indices off by 1
    flatIndex = [ownMap[i+1] for i in xrange(len(ownMap))]
    add_extrinsic(ModIndex, module, flatIndex)
    return module

def deserialize(digest):
    if digest in LOADED_MODULES:
        return LOADED_MODULES[digest]

    module = _read_module('mods/%s' % (digest,))

    add_extrinsic(ModDigest, module, digest)
    LOADED_MODULES[digest] = module

    if DIGEST_INDEX[digest] == 'forms':
        bind_form_representations(module.root)

    return module

def deserialize_bundle(name, overlays):
    digest = os.readlink('mods/%s_bundle' % (name,))
    bundle_mod = deserialize(digest)
    # TODO overlays
    return bundle_mod

BASIC_FORM_INDEX = {}

def save_form_meanings(forms):
    # this function is actually part of serialization
    # save {atom index -> true repr} mapping so that we can recover
    # meanings during deserialization
    assert not BASIC_FORM_INDEX, "Can't handle more than one module"

    def remember(src):
        pos = extrinsic(Location, src)
        assert pos.index not in BASIC_FORM_INDEX
        BASIC_FORM_INDEX[pos.index] = extrinsic(TrueRepresentation, src)

    for dt in forms:
        remember(dt)
        map_(remember, dt.ctors)

def bind_form_representations(dt_list):
    # retrieve form->true repr meanings via remembered indices
    # also write Names for convenience

    def lookup(o):
        return BASIC_FORM_INDEX[extrinsic(Location, o).index]

    for dt in dt_list.dts:
        true = lookup(dt)
        add_extrinsic(TrueRepresentation, dt, true)
        add_extrinsic(Name, dt, true.__name__)

        for ctor in dt.ctors:
            true = lookup(ctor)
            add_extrinsic(TrueRepresentation, ctor, true)
            add_extrinsic(Name, ctor, true.__name__)

            for field, name in ezip(ctor.fields, true.__slots__[:-1]):
                add_extrinsic(Name, field, name)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
