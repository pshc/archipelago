import base as _base

ModIndex = _base.new_extrinsic('ModIndex', [int])

Pos = _base.DT('Pos', ('module', '*Module'), ('index', int))

Location = _base.new_extrinsic('Location', Pos)

Overlay = _base.DT('Overlay', ('mapping', {'a': 'b'}))

Scheme = _base.DT('Scheme', ('tvars', [_base.TypeVar]), ('type', _base.Type))

TypeOf = _base.new_extrinsic('TypeOf', Scheme)

loaded_modules = {}
loaded_module_atoms = {}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
