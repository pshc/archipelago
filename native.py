from base import *
from bedrock import *
from globs import *
from hashlib import sha256
from os import system

ModuleMeta = DT('ModuleMeta', ('count', int), ('deps', [str]))

SerialState = DT('SerialState',
        ('file', file),
        ('hash', None),
        ('count', int),
        ('depmap', {Module: int}))

Serialize = new_env('Serialize', SerialState)

def _write(b):
    state = env(Serialize)
    state.file.write(b)
    state.hash.update(b)

def _write_ref(node, t):
    assert has_extrinsic(Location, node), \
            'Weak ref to unserialized: %r 0x%x' % (node, id(node))
    if isinstance(t, TVar):
        pass # Does it even make sense to check instantiations here?
    elif isinstance(t, TData):
        adt = extrinsic(FormBacking, t.data)
        assert isinstance(node, adt), "->%r is not a %s" % (node, adt)
    else:
        assert False, "%r is not a ref type" % (t,)
    loc = extrinsic(Location, node)
    b = _encode_int(loc.index)
    depmap = env(Serialize).depmap
    if loc.module not in depmap:
        # New module; new index
        a = len(depmap)
        depmap[loc.module] = a
        _write(_encode_int(a) + extrinsic(ModDigest, loc.module) + b)
    else:
        # Existing module; refer by index
        _write(_encode_int(depmap[loc.module]) + b)

def _encode_int(n):
    if n < 0x80:
        return chr(n)
    n -= 0x80
    if n < 0x4000:
        return chr(n>>8 | 0x80) + chr(n & 0xff)
    n -= 0x4000
    if n < 0x200000:
        return chr(n>>16 | 0xc0) + chr(n>>8 & 0xff) + chr(n & 0xff)
    n -= 0x200000
    if n < 0x10000000:
        return chr(n>>24 | 0xe0) + chr(n>>16 & 0xff) + \
                chr(n>>8 & 0xff) + chr(n & 0xff)
    n -= 0x10000000
    assert n < (0x100000000 - 0x10204080), "Int overflow"
    return chr(0xf0) + chr(n>>24 & 0xff) + chr(n>>16 & 0xff) + \
            chr(n>>8 & 0xff) + chr(n & 0xff)

def _encode_str(s):
    b = s.encode('UTF-8')
    return _encode_int(len(b)) + b

def _serialize_node(node, t):
    if isinstance(node, Structured):
        assert isinstance(t, TData), "%r is not a datatype" % (t,)
        env(Serialize).count += 1
        # Collect instantiations
        apps = {}
        for var, app in ezip(t.data.tvars, t.appTypes):
            apps[var] = app
        adt = extrinsic(FormBacking, t.data)
        assert isinstance(node, adt), "%r is not a %s" % (node, adt)
        # Possibly write discriminator
        if len(t.data.ctors) > 1:
            ix = node._ctor_ix
            _write(_encode_int(ix))
            form = t.data.ctors[node._ctor_ix]
        else:
            form = t.data.ctors[0]
        # Dump fields
        ctor = extrinsic(FormBacking, form)
        assert isinstance(node, ctor), "%r is not a %s" % (node, ctor)
        for field in form.fields:
            sub = getattr(node, extrinsic(Name, field))
            ft = field.type
            if isinstance(ft, TVar):
                assert ft.typeVar in apps, \
                        "Can't write free %r in %r with env %r" % (
                        ft, field, apps)
                ft = apps[ft.typeVar]
                assert not isinstance(ft, TWeak), "TVar instantiated weakly?"
            if isinstance(ft, TWeak):
                _write_ref(sub, ft.refType)
            else:
                _serialize_node(sub, ft)
    elif isinstance(node, basestring):
        assert isinstance(t, TPrim) and isinstance(t.primType, PStr)
        _write(_encode_str(node))
    elif isinstance(node, bool):
        assert isinstance(t, TPrim) and isinstance(t.primType, PBool)
        _write(_encode_int(1 if node else 0))
    elif isinstance(node, int):
        assert isinstance(t, TPrim) and isinstance(t.primType, PInt)
        _write(_encode_int(node))
    elif isinstance(node, list):
        assert isinstance(t, TArray), "Unexpected array:\n%s\nfor:\n%s" % (
                node, t)
        _write(_encode_int(len(node)))
        # TODO: Check list element type for weak
        for item in node:
            _serialize_node(item, t.elemType)
    else:
        assert False, "Can't serialize %r" % (node,)

InspectState = DT('InspectState', ('module', '*Module'), ('count', int))

Inspection = new_env('Inspection', InspectState)

def _inspect_node(node):
    if isinstance(node, Structured):
        assert not has_extrinsic(Location, node), "Multiply used %r" % (node,)
        state = env(Inspection)
        add_extrinsic(Location, node, Pos(state.module, state.count))
        state.count += 1
        form = node.__form__
        assert isinstance(form, Ctor)
        for field in form.fields:
            sub = getattr(node, extrinsic(Name, field))
            if not isinstance(field.type, TWeak):
                _inspect_node(sub)
    elif isinstance(node, list):
        for sub in node:
            _inspect_node(sub)

def _cmp_digest(a, b):
    return cmp(extrinsic(ModDigest, a), extrinsic(ModDigest, b))

ModInspection = DT('ModInspection', ('atomCount', int),
                                    ('deps', ['*Module']))

def inspect(module):
    inspect = InspectState(module, 0)
    in_env(Inspection, inspect, lambda: _inspect_node(module.root))
    return inspect.count

def serialize(module):
    assert not has_extrinsic(ModDigest, module)
    temp = '/tmp/serialize'
    hash = sha256()
    inspection_count = inspect(module)

    f = file(temp, 'wb')
    depmap = {module: 0}
    state = SerialState(f, hash, 0, depmap)
    in_env(Serialize, state,
            lambda: _serialize_node(module.root, module.rootType))
    f.close()

    hex = hash.digest().encode('hex')
    name = extrinsic(Name, module)
    system('mv -f -- %s mods/%s' % (temp, hex))
    system('ln -sf -- %s mods/%s' % (hex, name))

    del depmap[module]
    deps = depmap.items()
    deps.sort(lambda a, b: cmp(a[1], b[1]))
    deps = map(fst, deps)
    add_extrinsic(ModDeps, module, deps)
    add_extrinsic(ModDigest, module, hex)

    assert state.count == inspection_count, "Inconsistent atom count"
    meta = ModuleMeta(state.count, [extrinsic(ModDigest, d) for d in deps])
    f = file('opt/%s_meta' % (hex,), 'wb')
    in_env(Serialize, SerialState(f, sha256(), 0, None),
            lambda: _serialize_node(meta, t_DT(ModuleMeta)))
    f.close()
    system('ln -sf -- %s_meta opt/%s_meta' % (hex, name))

DeserialState = DT('DeserialState',
        ('file', file),
        ('module', Module),
        ('deps', {int: Module}),
        ('index', int),
        ('ownMap', {int: object}),
        ('forwardRefs', {int: [object]}))

Deserialize = new_env('Deserialize', DeserialState)

def _read_int():
    f = env(Deserialize).file
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

def _read_str():
    n = _read_int()
    return env(Deserialize).read(n).decode('UTF-8')

def _read_node(t, path):
    if isinstance(t, TData):
        state = env(Deserialize)
        index = state.index
        state.index += 1
        if len(t.ctors) > 1:
            ctor = t.ctors[_read_int()]
        else:
            ctor = t.ctors[0]
        form = ctor.__form__
        assert isinstance(form, Ctor)

        # Bleh.
        val = ctor(*[None for f in form.fields])
        state.ownMap[index] = val
        for field in form.fields:
            fnm = extrinsic(Name, field)
            child = _read_node(field.type, (val, fnm))
            setattr(val, fnm, child)

        return val
    elif matches(t, 'TPrim(PInt())'):
        return _read_int()
    elif matches(t, 'TPrim(PStr())'):
        return _read_str()
    elif isinstance(t, TApply):
        assert t.appTarget == list, 'TEMP'
        # TODO
        count = _read_int()
        array = []
        for i in xrange(count):
            array.append(_read_node(t.appVars[0], path + (i,)))
        return array
    elif isinstance(t, TWeak):
        state = env(Deserialize)
        depindex = _read_int()
        index = _read_int()
        if depindex == 0:
            if index in state.ownMap:
                return state.ownMap[index]
            else:
                # Resolve later
                state.forwardRefs.setdefault(index, []).append(path)
                return 'forward ref'
        else:
            return extrinsic(ModIndex, state.deps[depindex-1])[index]
    else:
        assert False, "%r is not a type" % (t,)

LOADED_MODULES = {}

def deserialize(digest, root_type):
    if digest in LOADED_MODULES:
        return LOADED_MODULES[digest]
    print 'deserialize', digest
    f = file('mods/%s' % (digest,), 'rb')
    deps = []
    module = Module('unknown', Just(digest), None)
    ownMap = {}
    forwardRefs = {}
    def go():
        dep_count = _read_int()
        for i in xrange(dep_count):
            hash = f.read(64) # hex
            dep = LOADED_MODULES.get(hash)
            if dep is None:
                dep = deserialize(hash)
            deps.append(dep)
        module.root = _read_node(root_type, (module, 'root'))
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
    state = DeserialState(f, module, deps, 0, ownMap, forwardRefs)
    in_env(Deserialize, state, go)
    f.close()
    ownMap = [v for k, v in sorted(ownMap.items())]
    add_extrinsic(ModIndex, module, ownMap)
    LOADED_MODULES[digest] = module
    return module

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
