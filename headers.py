from atom import *
import sys

HDR = new_env('HDR', None)

def out(s):
    env(HDR).write(s)
    if not env(GENOPTS).quiet:
        sys.stdout.write(s)

def write_type(t):
    out(match(t,
        ('TPrim(PInt() or PBool())', lambda: 'int'),
        ('TPrim(PFloat())', lambda: 'float'),
        ('TVoid()', lambda: 'void'),
        ('_', lambda: 'void *')))

def write_params(ps):
    if len(ps) == 0:
        out('(void)')
        return
    first = True
    out('(')
    for p in ps:
        if first:
            first = False
        else:
            out(', ')
        write_type(p)
    out(')')

def write_func_decl(name, params, ret):
    write_type(ret)
    out(' %s' % (name,))
    write_params(params)
    out(';\n')

def write_decls(decls, name):
    guard = name.upper() + '_H'
    out('#ifndef %s\n#define %s\n\n' % (guard, guard))
    for v in decls.funcDecls:
        t = extrinsic(TypeOf, v)
        name = extrinsic(Name, v)
        match(t, ('TFunc(params, ret, _)', lambda params, ret:
                    write_func_decl(name, params, ret)))
    out('\n#endif /* %s */\n' % (guard,))

def write_export_header(mod, header, cname):
    f = open(header, 'wb')
    in_env(HDR, f, lambda: write_decls(mod.root, cname))
    f.close()

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
