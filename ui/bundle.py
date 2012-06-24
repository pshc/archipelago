#!/usr/bin/env python
from os import mkdir, readlink, rename
from os.path import exists, join

FILES = ['bedrock', 'builtins', 'forms']
SRC = '..'
DEST = 'forms.bundle'

def mod(name):
    return join(SRC, 'mods', name)
def opt(name):
    return join(SRC, 'opt', name)

def to_dest(full):
    return DEST + full[len(SRC):]

def package(files):
    found = []
    full = []
    for f in files:
        p = mod(f)
        assert exists(p)
        found.append(f)
        full.append(p)
        nm = p + '_Name'
        if exists(nm):
            full.append(nm)
            found.append(f + '_Name')
    for f in full[:]:
        dest = readlink(f)
        full.append(mod(dest))
    for f in found:
        p = opt(f + '_meta')
        full += [p, opt(readlink(p))]

    for f in full:
        print f
        rename(f, to_dest(f))

def make_dir(d):
    if not exists(d):
        mkdir(d)

def setup():
    make_dir(DEST)
    make_dir(join(DEST, 'mods'))
    make_dir(join(DEST, 'opt'))

setup()
package(FILES)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
