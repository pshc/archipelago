import base

ModIndex = base.new_extrinsic('ModIndex', [int])
Filename = base.new_extrinsic('Filename', str)

Pos = base.DT('Pos', ('module', '*Module'), ('index', int))

Location = base.new_extrinsic('Location', Pos)

TypeOf = base.new_extrinsic('TypeOf', base.Type)
TypeVars = base.new_extrinsic('TypeVars', [base.TypeVar])

InstMap = base.new_extrinsic('InstMap', {base.TypeVar: base.Type})

loaded_modules = {}
loaded_module_atoms = {}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
