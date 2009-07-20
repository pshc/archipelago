# "Standard library" builtins
import base as __base

(Atom, Int, Str, Ref) = __base.ADT('Atom',
                            'Int', ('intVal', int), ('subs', ['Atom']),
                            'Str', ('strVal', str), ('subs', ['Atom']),
                            'Ref', ('refAtom', 'Atom'), ('refMod', 'Module'),
                                   ('subs', ['Atom']))

class ArrayAtom:
    __slots__ = ('_ix', 'val', 'ptr', 'nsubs')
    def __init__(self):
        self._ix = -1
        self.val = self.ptr = self.nsubs = 0
    def __repr__(self):
        d = {'ix': self._ix, 'val': self.val, 'ptr': self.ptr, 'n': self.nsubs}
        if self._ix == 2:
            d['modNm'] = self.ptr.modName
        return {-1: '<null atom>', 2: 'ref(%(val)d, %(modNm)s, %(n)d)',
                1: 'str(%(ptr)s, %(n)d)', 0: 'int(%(val)d, %(n)d)'} \
               .get(self._ix, 'wtf(%(ix)d)') % d

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

from os import system
fgetc = lambda f: f.read(1)
fputc = lambda f, c: f.write(c)
fwrite = lambda f, d: f.write(d)
def fread(buf, sz, n, f):
    for i in range(n):
        buf[i] = f.read(sz)
    return n
fopen = open
fclose = lambda f: f.close()
sizeof = len
hint = lambda x: x
def stringify(buf):
    try:
        n = buf.index('\0')
    except ValueError:
        assert False, 'buf is not null-terminated'
    return ''.join(buf[:n])

from hashlib import sha256

builtins = dict((k, v) for k, v in locals().iteritems()
                       if not k.startswith('__'))

builtins.update(dict((b, __builtins__[b]) for b in [
    'None', 'True', 'False', 'sorted', 'getattr', 'ord', 'range', 'len',
    ]))

builtins.update(dict((dummy, None) for dummy in [
    '_ix', 'val', 'ptr', 'nsubs',
    'hexdigest', 'keys', 'update']))

def bi_print(s): print s

def make_record():
    class Record(object):
        pass
    return Record

import operator as o
builtins.update({'+': o.add, '-': o.sub, '*': o.mul, '%': o.mod,
                'negate': o.neg, '==': o.eq, '!=': o.ne, '<': o.lt, '>': o.gt,
                '<=': o.le, '>=': o.ge, 'is': o.is_, 'is not': o.is_not,
                'in': lambda x, y: x in y, 'not in': lambda x, y: x not in y,
                'slice': o.getslice,
                'print': bi_print,
                'object': make_record,
                'identity': lambda x: x,
                'tuple2': lambda x, y: (x, y),
                'tuple3': lambda x, y, z: (x, y, z),
                'tuple4': lambda w, x, y, z: (w, x, y, z),
                'tuple5': lambda v, w, x, y, z: (v, w, x, y, z),
                'to_void': lambda p: p,
                })

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
