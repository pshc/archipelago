funcs = """
glClear
glClearColor
glCreateShader
glCompileShader
glDeleteShader
glGetShaderiv
glShaderSource
glUniformMatrix4fv
"""

consts = """
GL_COLOR_BUFFER_BIT
GL_COMPILE_STATUS
GL_INFO_LOG_LENGTH
"""

overrides = """
glShaderSource :: (int, int, [str], Maybe([int])) -> void
"""
