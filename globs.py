from base import *

Overlay = DT('Overlay', ('annotate', 'Atom -> str'))

TypeAnnot = Overlay(repr)
CastAnnot = Overlay(lambda t: '.. => %r' % t)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
