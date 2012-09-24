import base

ModIndex = base.new_extrinsic('ModIndex', [int])
Filename = base.new_extrinsic('Filename', str)

Pos = base.DT('Pos', ('module', '*Module'), ('index', int))

Location = base.new_extrinsic('Location', Pos, omni=True)

TypeOf = base.new_extrinsic('TypeOf', base.Type, omni=True)
TypeVars = base.new_extrinsic('TypeVars', [base.TypeVar])

Instantiation = base.new_extrinsic('Instantiation', {'*TypeVar': base.Type})
TypeCast = base.new_extrinsic('TypeCast', (base.Type, base.Type))
InstMap = base.new_extrinsic('InstMap', {base.TypeVar: base.Type})

loaded_modules = {}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
