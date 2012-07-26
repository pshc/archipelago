glClear = cdecl('glClear', 'int -> void')
glClearColor = cdecl('glClearColor', '(float, float, float, float) -> void')
glUniformMatrix4fv = cdecl('glUniformMatrix4fv',
        '(int, int, bool, [float]) -> void')

GL_COLOR_BUFFER_BIT = 16384

