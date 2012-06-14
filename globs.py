import base

ModIndex = base.new_extrinsic('ModIndex', [int])

Pos = base.DT('Pos', ('module', '*Module'), ('index', int))

Location = base.new_extrinsic('Location', Pos)

# TEMP
Entry = base.DT('Entry', ('key', '*a'), ('value', str))
Overlay = base.DT('Overlay', ('mapping', [Entry]))

TypeOf = base.new_extrinsic('TypeOf', base.Type)

GenOpts = base.DT('GenOpts', ('quiet', bool))
GENOPTS = base.new_env('GENOPTS', GenOpts)

loaded_modules = {}
loaded_module_atoms = {}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
