import base

Overlay = base.DT('Overlay', ('annotate', 'Atom -> str'))

TypeAnnot = Overlay(repr)
CastAnnot = Overlay(lambda t: '.. => %r' % t)

PropAnnot = Overlay(repr)
PROP_ANNOT = {}

loaded_modules = {}
loaded_module_atoms = {}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
