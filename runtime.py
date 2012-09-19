# Just the bare minimum to bootstrap bedrock

malloc = cdecl('malloc', 'int -> a')
_addextrinsic = cdecl('_addextrinsic', '(e, a, b) -> void')
_updateextrinsic = cdecl('_updateextrinsic', '(e, a, b) -> void')
_getextrinsic = cdecl('_getextrinsic', '(e, a) -> b')
_hasextrinsic = cdecl('_hasextrinsic', '(e, a) -> bool')

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
