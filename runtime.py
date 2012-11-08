# Just the bare minimum to bootstrap bedrock

malloc = cdecl('malloc', 'int -> a')
free = cdecl('free', 'a -> void')
fail = cdecl('fail', 'str -> noreturn')
match_fail = cdecl('match_fail', 'void -> noreturn')

_getenv = cdecl('_getenv', '(Env, c) -> a')
_haveenv = cdecl('_haveenv', '(Env, c) -> bool')
_pushenv = cdecl('_pushenv', '(Env, c, v) -> c')
_popenv = cdecl('_popenv', '(Env, c) -> c')

_addextrinsic = cdecl('_addextrinsic', '(Extrinsic, a, b) -> void')
_updateextrinsic = cdecl('_updateextrinsic', '(Extrinsic, a, b) -> void')
_getextrinsic = cdecl('_getextrinsic', '(Extrinsic, a) -> b')
_hasextrinsic = cdecl('_hasextrinsic', '(Extrinsic, a) -> bool')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
