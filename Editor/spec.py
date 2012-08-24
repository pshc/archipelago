funcs = """
glAttachShader
glBindAttribLocation
glClear
glClearColor
glCreateProgram
glCreateShader
glCompileShader
glDeleteProgram
glDeleteShader
glDetachShader
glLinkProgram
glGetProgramiv
glGetShaderInfoLog
glGetShaderiv
glShaderSource
glUniformMatrix4fv
"""

consts = """
GL_COLOR_BUFFER_BIT
GL_COMPILE_STATUS
GL_FRAGMENT_SHADER
GL_INFO_LOG_LENGTH
GL_LINK_STATUS
GL_VERTEX_SHADER
"""

overrides = """
glShaderSource :: (int, int, [str], Maybe([int])) -> void
"""
