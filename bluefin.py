gc_alloc = cdecl('gc_alloc', 'int -> a')
gc_array = cdecl('gc_array', 'int -> [a]')
gc_array_ptr = cdecl('gc_array_ptr', '[a] -> b')
gc_array_len = cdecl('gc_array_len', '[a] -> int')
gc_array_subscript = cdecl('gc_array_subscript', '([a], int) -> a')
