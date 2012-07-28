#!/usr/bin/env python2
import io
import re
import subprocess

def macro_values(input, prefix):
    c = subprocess.check_output(['clang', '-E', '-dM', input])
    for line in c.splitlines():
        m = re.match(r'^#define\s+('+prefix+r'\w+)\s+([\da-fA-Fx]+)$', line)
        if m:
            print m.group(1), '=', m.group(2)

def func_decls(input, prefix):
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
            parse_func_decl(list(tokenize(m.group(1))), typedefs, prefix)

def parse_func_decl(s, typedefs, prefix):
    line = ' '.join(s)
    tvars = []
    retT = consume_type(s, typedefs, tvars)
    name = s.pop(0)
    assert s[0] == '(', "Couldn't parse retT of "+line+" at: " + ' '.join(s)
    s.pop(0)
    if not name.startswith(prefix):
        return
    if 'Sync' in name: # XXX skip structs
        return
    argTs = []
    while s[0] != ')':
        argTs.append(consume_type(s, typedefs, tvars))
        if s[0] not in ',)':
            argNm = s.pop(0)
        if s[0] == ',':
            s.pop(0)
        else:
            assert s[0] == ')', "Expected comma, got " + ' '.join(s)
    assert s == [')', ';'], 'Unexpected trailer: ' + ' '.join(s)

    # XXX ignore variants for now
    for t in argTs:
        if 'double' in t or 'short' in t or 'char' in t or 'longlong' in t:
            return

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
                t = '[%s]' % (t,)
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
            t = 'str' if t == 'char' else '[%s]' % (t,)
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

if __name__ == '__main__':
    func_decls('gl.c', 'gl')
    macro_values('gl.c', 'GL_')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
