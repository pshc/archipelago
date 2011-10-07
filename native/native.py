from base import *
from hashlib import sha256
from os import system

Maybe, Just, Nothing = ADT('Maybe', 'Just', ('just', 'a'), 'Nothing')
def isJust(m): return match(m, ('Just(_)', lambda: True), ('_', lambda: False))
def isNothing(m): return match(m, ('Nothing()', lambda: True),
                                  ('_', lambda: False))

Module = DT('Module', ('name', str), ('digest', str), ('root', 'a'))

ModIndex = new_extrinsic('ModIndex', list)

Var = DT('Var')

AST, Num, Bind, Plus, Lam, App = ADT('AST',
        'Num', ('int', int),
        'Bind', ('var', '*Var'),
        'Plus', ('a', 'AST'), ('b', 'AST'),
        'Lam', ('param', Var), ('expr', 'AST'),
        'App', ('func', 'AST'), ('arg', 'AST'))

Ptr = DT('Ptr', ('dest', 'a'))

# Var' = Var w/ name annotations
# AST' = AST w/ Var'

Name = new_extrinsic('Name', str)

def nameof(node):
    return extrinsic(Name, node)

Pos = DT('Pos', ('module', Module), ('index', int))

Location = new_extrinsic('Location', Pos)

SerialState = DT('SerialState',
        ('file', file),
        ('hash', None),
        ('index', int),
        ('deps', dict))

Serialize = new_context('Serialize', SerialState)

def _write(b):
    state = context(Serialize)
    state.file.write(b)
    state.hash.update(b)

def _write_ref(node):
    assert isinstance(node, Ptr), 'Expected Ptr, got %r' % (node,)
    node = node.dest
    if has_extrinsic(OwnIndex, node):
        a = 0
        b = extrinsic(OwnIndex, node)
    elif has_extrinsic(Location, node):
        state = context(Serialize)
        loc = extrinsic(Location, node)
        a = state.deps[loc.module]
        b = loc.index
    else:
        assert False, 'Ptr to unserialized: %r' % (node,)
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
        for (field, type) in zip(node.__slots__[:-1], node.__types__):
            sub = getattr(node, field)
            if isinstance(type, TRef):
                _write_ref(sub)
            else:
                _serialize_node(sub)
    else:
        if isinstance(node, basestring):
            b = _encode_str(node)
        elif isinstance(node, int):
            b = _encode_int(node)
        else:
            assert False, "Can't serialize %r" % (node,)
        _write(b) # can't refer to these...

InspectState = DT('InspectState',
        ('count', int),
        ('deps', set),
        )

Inspection = new_context('Inspection', InspectState)

# XXX: Abuse of extrinsics. They are global.
OwnIndex = new_extrinsic('OwnIndex', int)

def _inspect_node(node):
    if isinstance(node, DataType):
        assert not has_extrinsic(Location, node), "Already serialized?!"
        state = context(Inspection)
        add_extrinsic(OwnIndex, node, state.count)
        state.count += 1
        for (field, type) in zip(node.__slots__[:-1], node.__types__):
            sub = getattr(node, field)
            if isinstance(type, TRef):
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
        ('deps', dict),
        ('index', int),
        ('ownMap', list),
        ('forwardRefs', dict))

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

def _read_node(t):
    if isinstance(t, __builtins__.type) and issubclass(t, DataType):
        state = context(Deserialize)
        index = state.index
        state.index += 1
        ctor = t.ctors[_read_int()]

        fields = []
        for type in ctor.__types__:
            child = _read_node(type)
            fields.append(child)
        val = ctor(*fields)
        state.ownMap[index] = val

        add_extrinsic(Location, val, Pos(state.module, index))
        return val
    else:
        if isinstance(t, TInt):
            return _read_int()
        elif isinstance(t, TStr):
            return _read_str()
        elif isinstance(t, TRef):
            state = context(Deserialize)
            depindex = _read_int()
            index = _read_int()
            if depindex == 0:
                if False or index in state.ownMap:
                    return Ptr(state.ownMap[index])
                else:
                    # Resolve later
                    ptr = Ptr(None)
                    state.forwardRefs.setdefault(index, []).append(ptr)
                    return ptr
            else:
                return Ptr(extrinsic(ModIndex, state.deps[depindex-1])[index])
        else:
            assert False, "%r is not a type" % (t,)

LOADED_MODULES = {}

def deserialize(digest, root_type=AST):
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
        module.root = _read_node(root_type)
        for index, ptrs in forwardRefs.iteritems():
            dest = ownMap[index]
            for ptr in ptrs:
                ptr.dest = dest
        return module
    state = DeserialState(f, module, deps, 0, ownMap, forwardRefs)
    in_context(Deserialize, state, go)
    f.close()
    ownMap = [v for k, v in sorted(ownMap.items())]
    add_extrinsic(ModIndex, module, ownMap)
    LOADED_MODULES[digest] = module
    return module

def test():
    foo = Var()
    add_extrinsic(Name, foo, 'foo')
    body = Plus(Num(1), Bind(Ptr(foo)))
    sample = Plus(Bind(Ptr(foo)), App(Lam(foo, body), Num(0x3042)))

    print 'before', sample
    module = Module('test', Nothing(), sample)
    serialize(module)
    print 'digest', module.digest.just
    module = deserialize(module.digest.just)
    print 'after', module.root

def main():
    scope_extrinsic(Name,
            lambda: scope_extrinsic(Location,
            lambda: scope_extrinsic(ModIndex, test)))
    return 0

if __name__ == '__main__':
    main()