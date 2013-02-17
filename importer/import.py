#!/usr/bin/env python2
import io
import re
import subprocess

def macro_values(input, spec):
    c = subprocess.check_output(['clang', '-E', '-dM', input])
    for line in c.splitlines():
        m = re.match(r'^#define\s+(\w+)\s+([\da-fA-Fx]+)$', line)
        if m:
            name, val = m.groups()
            if name in spec.consts:
                print name, '=', m.group(2)

def func_decls(input, spec):
    c = subprocess.check_output(['clang', '-cc1', '-ast-print', input])
    typedefs = {}
    for line in c.splitlines():
        m = re.match(r'^typedef\s+(.*?\s+\**)(\w+);\s*$', line)
        if m:
            t, name = m.groups()
            if name == 'GLboolean':
                t = 'bool'
            typedefs[name] = t.strip()
            continue
        m = re.match(r'^extern\s+(.*)', line)
        if m:
            parse_func_decl(list(tokenize(m.group(1))), typedefs, spec)

def parse_func_decl(s, typedefs, spec):
    line = ' '.join(s)
    tvars = []
    retT = consume_type(s, typedefs, tvars)
    name = s.pop(0)
    assert s[0] == '(', "Couldn't parse retT of "+line+" at: " + ' '.join(s)
    s.pop(0)
    if name not in spec.funcs:
        return
    overrides = spec.overrides.get(name, {})

    argTs = []
    while s[0] != ')':
        toks = s[:]
        argT = consume_type(s, typedefs, tvars)
        toks = toks[:len(toks) -  len(s)]
        if s[0] not in ',)':
            argT = overrides.get(s.pop(0), argT)
        argTs.append(argT)
        if s[0] == ',':
            s.pop(0)
        else:
            assert s[0] == ')', "Expected comma, got " + ' '.join(s)
    assert s == [')', ';'], 'Unexpected trailer: ' + ' '.join(s)

    if len(argTs) > 1:
        typedesc = '(%s) -> %s' % (', '.join(argTs), retT)
    else:
        arg = argTs[0] if argTs else 'void'
        typedesc = '%s -> %s' % (arg, retT)

    decl = '%s = cdecl(%r, %r)' % (name, name, typedesc)
    if len(decl) > 79:
        decl = '%s = cdecl(%r,\n\t%r)' % (name, name, typedesc)
    print decl

IGNORED_QUALIFIERS = ['const', 'signed', 'unsigned']

def consume_type(toks, typedefs, tvars):
    t = None

    while toks[0] in IGNORED_QUALIFIERS:
        toks.pop(0)
    tok = toks[0]

    # Recurse into typedefs
    if tok in typedefs:
        toks[:1] = tokenize(typedefs[tok])
        return consume_type(toks, typedefs, tvars)

    if tok == 'void':
        toks.pop(0)
        if toks[0] == '*':
            toks.pop(0)
            t = chr(97 + len(tvars))
            tvars.append(t)
            while toks[0] == '*':
                toks.pop(0)
                t = 'b[%s]' % (t,)
        else:
            t = 'void'
    else: # Normal type

        # Structs not supported yet
        if tok == 'struct':
            toks.pop(0)
            tok = toks[0]

        toks.pop(0)
        if tok == 'long':
            if toks[0] == 'long':
                tok = 'longlong'
                toks.pop(0)
            else:
                tok = 'int'
        t = tok
        while toks[0] == '*':
            toks.pop(0)
            t = 'str' if t == 'char' else 'r[%s]' % (t,)
    return t


def expand_type(t, typevars):
    pass

def tokenize(s):
    word = ''
    for c in s:
        if re.match(r'\w', c):
            word += c
        else:
            if word:
                yield word
                word = ''
            if not re.match(r'\s', c):
                yield c
    if word:
        yield word

def parse_overrides(line):
    func, args = re.match(r'^\s*(\w+)\s+(.+?)\s*$', line).groups()
    args = dict(re.match(r'^\s*(\w+)\s*::\s*(.+?)\s*$', s).groups()
                for s in args.split(';'))
    return (func, args)

def load_spec(filename):
    import imp
    spec = imp.load_source('spec', filename)
    spec.funcs = re.findall(r'\w+', spec.funcs)
    spec.consts = re.findall(r'\w+', spec.consts)
    lines = filter(None, spec.overrides.splitlines())
    spec.overrides = dict(map(parse_overrides, lines))
    return spec

if __name__ == '__main__':
    import inspect, os.path, sys
    spec = load_spec(sys.argv[1])
    path = os.path.dirname(inspect.getfile(inspect.currentframe()))
    gl_c = os.path.join(path, 'gl.c')
    print 'from maybe import *'
    func_decls(gl_c, spec)
    macro_values(gl_c, spec)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
