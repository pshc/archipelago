import base as _base

ModIndex = _base.new_extrinsic('ModIndex', [int])

Pos = _base.DT('Pos', ('module', '*Module'), ('index', int))

Location = _base.new_extrinsic('Location', Pos)

# TEMP
Entry = _base.DT('Entry', ('key', '*a'), ('value', str))
Overlay = _base.DT('Overlay', ('mapping', [Entry]))

TypeOf = _base.new_extrinsic('TypeOf', _base.Type)

loaded_modules = {}
loaded_module_atoms = {}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
