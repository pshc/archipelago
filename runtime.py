from base import cdecl
# Just the bare minimum to bootstrap bedrock

malloc = cdecl('malloc', 'int -> a')
free = cdecl('free', 'a -> void')
fail = cdecl('fail', 'str -> noreturn')
fail_with_code = cdecl('fail_with_code', 'int -> noreturn')

_getenv = cdecl('_getenv', '(Env, c) -> a')
_haveenv = cdecl('_haveenv', '(Env, c) -> bool')
_pushenv = cdecl('_pushenv', '(Env, c, v) -> c')
_popenv = cdecl('_popenv', '(Env, c) -> c')

_addextrinsic = cdecl('_addextrinsic', '(Extrinsic, a, b) -> void')
_updateextrinsic = cdecl('_updateextrinsic', '(Extrinsic, a, b) -> void')
_getextrinsic = cdecl('_getextrinsic', '(Extrinsic, a) -> b')
_hasextrinsic = cdecl('_hasextrinsic', '(Extrinsic, a) -> bool')

# TEMP
puts = cdecl('puts', 'str -> void')
_print_str = cdecl('_print_str', 'str -> void')
_print_int = cdecl('_print_int', 'int -> void')
_newline = cdecl('_newline', 'void -> void')

FAIL_BAD_MATCH = 100

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
