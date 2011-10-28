#!/usr/bin/env python
from base import *
from bedrock import *
from native import *

Var = DT('Var')

AST, Num, Bind, Plus, Lam, App = ADT('AST',
        'Num', ('int', int),
        'Bind', ('var', '*Var'),
        'Plus', ('exprs', ['AST']),
        'Lam', ('param', Var), ('expr', 'AST'),
        'App', ('func', 'AST'), ('arg', 'AST'))

# Var' = Var w/ name annotations
# AST' = AST w/ Var'

def test():
    foo = Var()
    add_extrinsic(Name, foo, 'foo')
    body = Plus([Num(1), Num(2), Bind(foo)])
    sample = Plus([Bind(foo), App(Lam(foo, body), Num(0x3042))])

    print 'before', sample
    module = Module('test', Nothing(), sample)
    serialize(module)
    print 'digest', module.digest.just
    module = deserialize(module.digest.just, TData(AST))
    print 'after', module.root

def main():
    scope_extrinsic(Name,
            lambda: scope_extrinsic(Location,
            lambda: scope_extrinsic(ModIndex, test)))
    return 0

if __name__ == '__main__':
    main()

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
