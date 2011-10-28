from base import *
from bedrock import *
from globs import *
from hashlib import sha256
from os import system

SerialState = DT('SerialState',
        ('file', file),
        ('hash', None),
        ('index', int),
        ('deps', {Module: int}))

Serialize = new_context('Serialize', SerialState)

def _write(b):
    state = context(Serialize)
    state.file.write(b)
    state.hash.update(b)

def _write_ref(node):
    if has_extrinsic(OwnIndex, node):
        a = 0
        b = extrinsic(OwnIndex, node)
    elif has_extrinsic(Location, node):
        state = context(Serialize)
        loc = extrinsic(Location, node)
        a = state.deps[loc.module]
        b = loc.index
    else:
        assert False, 'Weak ref to unserialized: %r' % (node,)
    _write(_encode_int(a) + _encode_int(b))

def _encode_int(n):
    return unichr(n).encode('UTF-8')

def _encode_str(s):
    b = s.encode('UTF-8')
    return _encode_int(len(b)) + b

def _serialize_node(node):
    if isinstance(node, DataType):
        ix = getattr(node, '_ctor_ix', 0)
        _write(_encode_int(ix))
        for (field, t) in zip(node.__slots__[:-1], node.__types__):
            sub = getattr(node, field)
            if isinstance(t, TWeak):
                _write_ref(sub)
            else:
                _serialize_node(sub)
    elif isinstance(node, basestring):
        _write(_encode_str(node))
    elif isinstance(node, int):
        _write(_encode_int(node))
    elif isinstance(node, list):
        _write(_encode_int(len(node)))
        # TODO: Check list element type for weak
        for item in node:
            _serialize_node(item)
    else:
        assert False, "Can't serialize %r" % (node,)

InspectState = DT('InspectState',
        ('count', int),
        ('deps', set([str])),
        )

Inspection = new_context('Inspection', InspectState)

# XXX: Abuse of extrinsics. They are global.
OwnIndex = new_extrinsic('OwnIndex', int)

def _inspect_node(node):
    if isinstance(node, DataType):
        assert not has_extrinsic(Location, node), "Already serialized?!"
        assert not has_extrinsic(OwnIndex, node), "Multiply used %r" % (node,)
        state = context(Inspection)
        add_extrinsic(OwnIndex, node, state.count)
        state.count += 1
        for (field, t) in zip(node.__slots__[:-1], node.__types__):
            sub = getattr(node, field)
            if isinstance(t, TWeak):
                # Record this ref's target digest
                if has_extrinsic(Location, sub):
                    mod = extrinsic(Location, sub).module
                    state.deps.add(mod.digest.just)
            else:
                _inspect_node(sub)
    elif isinstance(node, list):
        for sub in node:
            _inspect_node(sub)

def serialize(module):
    assert isNothing(module.digest)
    temp = '/tmp/serialize'
    hash = sha256()
    def index():
        inspect = InspectState(0, set())
        in_context(Inspection, inspect, lambda: _inspect_node(module.root))
        f = file(temp, 'wb')
        deps = []
        depmap = {}
        for mod in sorted(inspect.deps,
                          lambda x, y: cmp(x.digest.just, y.digest.just)):
            deps.append(mod.digest)
            depmap[mod] = len(deps) # one-based
        state = SerialState(f, hash, 0, depmap)
        def go():
            _write(_encode_int(len(deps)))
            map_(_write, deps)
            _serialize_node(module.root)
        in_context(Serialize, state, go)
        f.close()
    scope_extrinsic(OwnIndex, index)
    hex = hash.digest().encode('hex')
    module.digest = Just(hex)
    system('mv -f -- %s mods/%s' % (temp, hex))
    system('ln -sf -- %s mods/%s' % (hex, module.name))

DeserialState = DT('DeserialState',
        ('file', file),
        ('module', Module),
        ('deps', {int: Module}),
        ('index', int),
        ('ownMap', {int: object}),
        ('forwardRefs', {int: [object]}))

Deserialize = new_context('Deserialize', DeserialState)

def _read_int():
    # TODO: Check extension chars for prefix
    f = context(Deserialize).file
    a = ord(f.read(1))
    if a <= 0b01111111:
        return a
    elif a <= 0b10111111:
        assert False, "Invalid extension char"
    elif a <= 0b11011111:
        b = ord(f.read(1))
        a = ((a & 0b00011111)<<6) | (b & 0b00111111)
        assert a > 0b01111111
        return a
    elif a <= 0b11101111:
        b, c = [ord(c) & 0b00111111 for c in f.read(2)]
        a = ((a & 0b00001111)<<12) | (b<<6) | c
        assert a > 0b11111111111
        return a
    elif a <= 0b11110111:
        b, c, d = [ord(c) & 0b00111111 for c in f.read(3)]
        a = ((a & 0b00000111)<<18) | (b<<12) | (c<<6) | d
        assert a > 0b1111111111111111
        return a
    else:
        assert False, "TODO"

def _read_str():
    n = _read_int()
    return context(Deserialize).read(n).decode('UTF-8')

def _read_node(t, path):
    if isinstance(t, TData):
        state = context(Deserialize)
        index = state.index
        state.index += 1
        ctor = t.data.ctors[_read_int()]

        # Bleh.
        val = ctor(*[None for t in ctor.__types__])
        state.ownMap[index] = val
        for fnm, ft in zip(ctor.__slots__[:-1], ctor.__types__):
            child = _read_node(ft, (val, fnm))
            setattr(val, fnm, child)

        add_extrinsic(Location, val, Pos(state.module, index))
        return val
    elif isinstance(t, TInt):
        return _read_int()
    elif isinstance(t, TStr):
        return _read_str()
    elif isinstance(t, TApply):
        assert t.appType == list, 'TEMP'
        count = _read_int()
        array = []
        for i in xrange(count):
            array.append(_read_node(t.appVars[0], path + (i,)))
        return array
    elif isinstance(t, TWeak):
        state = context(Deserialize)
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
    in_context(Deserialize, state, go)
    f.close()
    ownMap = [v for k, v in sorted(ownMap.items())]
    add_extrinsic(ModIndex, module, ownMap)
    LOADED_MODULES[digest] = module
    return module

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
