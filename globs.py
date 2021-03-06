import base

ModIndex = base.new_extrinsic('ModIndex', [int])
Filename = base.new_extrinsic('Filename', str)

Module = base.DT('Module', ('rootType', 'Type'), ('root', 'a'))

Pos = base.DT('Pos', ('module', '*Module'), ('index', int))
Location = base.new_extrinsic('Location', Pos, omni=True)

TypeOf = base.new_extrinsic('TypeOf', base.Type, omni=True)
TypeVars = base.new_extrinsic('TypeVars', [base.TypeVar])

ResultOf = base.new_extrinsic('ResultOf', base.Result, omni=True)

# if not present, assumed to be GC if boxed
LifeInfo, Heap, Stack = base.ADT('LifeInfo', 'Heap', 'Stack')
Life = base.new_extrinsic('Life', LifeInfo, omni=True)

Instantiation = base.new_extrinsic('Instantiation', {'*TypeVar': base.Type})
TypeCast = base.new_extrinsic('TypeCast', (base.Type, base.Type))
InstMap = base.new_extrinsic('InstMap', {base.TypeVar: base.Type})

GlobalInfo = base.DT('GlobalInfo', ('symbol', str), ('isFunc', bool))
GlobalSymbol = base.new_extrinsic('GlobalSymbol', GlobalInfo)
LocalSymbol = base.new_extrinsic('LocalSymbol', str)
FieldSymbol = base.new_extrinsic('FieldSymbol', str)

WRITTEN_MODULES = {}

RUNTIME_MODULE_OBJS = {
    'runtime.py': 'ir/z.o',
    'gc/interface.py': 'ir/gc_runtime.o',
}

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
