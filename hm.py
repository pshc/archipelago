#!/usr/bin/env python
from atom import *
from base import *
from builtins import *

add_sym('type')

def unknown_infer(a):
    assert False, 'Unknown type for:\n%s' % (a,)

def infer(a):
    t = match(a,
        ("Int(_, _)", lambda: 'int'),
        ("Str(_, _)", lambda: 'str'),
        ("key('DT', _)", lambda: None),
        ("otherwise", unknown_infer))
    if t is not None:
        if isinstance(t, basestring):
            t = symref(t, [])
        a.subs.append(symref('type', [t]))
    return a

def infer_types(roots):
    return map(infer, roots)

if __name__ == '__main__':
    import ast
    short = ast.convert_file('short.py')
    infer_types(short.roots)
    f = fopen('hello', 'w')
    for r in short.roots:
        fwrite(f, repr(r))
    fclose(f)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
