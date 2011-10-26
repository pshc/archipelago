import base as _base

ModIndex = _base.new_extrinsic('ModIndex', list)

Pos = _base.DT('Pos', ('module', 'Module'), ('index', int))

Location = _base.new_extrinsic('Location', Pos)

Overlay = _base.DT('Overlay', ('annotate', 'a -> str'))

TypeAnnot = Overlay(repr)
CastAnnot = Overlay(lambda t: '.. => %r' % t)

FuncAnnot = Overlay(lambda fs: 'w/ helpers: ' + repr(fs))
ExTypeAnnot = Overlay(lambda t: '(expanded lambda)')
ExLambdaAnnot = Overlay(lambda x: '(named)')

PropAnnot = Overlay(repr)
PROP_ANNOT = {}

loaded_modules = {}
loaded_module_atoms = {}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
