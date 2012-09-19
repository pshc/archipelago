malloc = cdecl('malloc', 'int -> a')
_addextrinsic = cdecl('_addextrinsic', '(e, a, b) -> void')
_updateextrinsic = cdecl('_updateextrinsic', '(e, a, b) -> void')
_getextrinsic = cdecl('_getextrinsic', '(e, a) -> b')
_hasextrinsic = cdecl('_hasextrinsic', '(e, a) -> bool')

# TEMP
_print_str = cdecl('_print_str', 'str -> void')
_print_int = cdecl('_print_int', 'int -> void')
_newline = cdecl('_newline', 'void -> void')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
