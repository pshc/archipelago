# "Standard library" builtins
class ArrayAtom:
    __slots__ = ('_ix', 'val', 'ptr', 'nsubs')
    def __init__(self):
        self._ix = self.val = self.ptr = self.nsubs = 0

def array(t, n):
    if t == 'char':
        return ['\0'] * n
    elif t == 'str':
        return [""] * n
    elif t == 'Atom':
        return [ArrayAtom() for i in range(n)]
    elif t == 'Module':
        return [None] * n
    assert False, 'Unknown array type %s' % t

fgetc = lambda f: f.read(1)
def fread(buf, sz, n, f):
    for i in range(n):
        buf[i] = f.read(sz)
    return n
fopen = open
fclose = lambda f: f.close()
sizeof = len
range = range
hint = lambda x: x
def stringify(buf):
    try:
        n = buf.index('\0')
    except ValueError:
        assert False, 'buf is not null-terminated'
    return ''.join(buf[:n])

builtins = dict((k, v) for k, v in locals().iteritems()
                       if not k.startswith('__'))

# Builtins that are a part of the compiler
builtins.update({'None': None, 'True': True, 'False': False, '_ix': None})

def bi_print(s): print s

def make_record():
    class Record(object):
        pass
    return Record

builtinFuncs = {'+': lambda x, y: x + y, '-': lambda x, y: x - y,
                '*': lambda x, y: x * y, '%': lambda x, y: x % y,
                'negate': lambda x: -x,
                '==': lambda x, y: x == y, '!=': lambda x, y: x != y,
                '<': lambda x, y: x < y, '>': lambda x, y: x > y,
                '<=': lambda x, y: x <= y, '>=': lambda x, y: x >= y,
                'is': lambda x, y: x is y, 'is not': lambda x, y: x is not y,
                'in': lambda x, y: x in y, 'not in': lambda x, y: x not in y,
                'slice': lambda l, d, u: l[d:u], 'len': lambda x: len(x),
                'print': bi_print,
                'object': make_record, 'getattr': getattr,
                'identity': lambda x: x, 'ord': ord,
                'tuple2': lambda x, y: (x, y),
                'tuple3': lambda x, y, z: (x, y, z),
                'tuple4': lambda w, x, y, z: (w, x, y, z),
                'tuple5': lambda v, w, x, y, z: (v, w, x, y, z),
                'to_void': lambda p: p,
                }
builtins.update(builtinFuncs)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
