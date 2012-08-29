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
glDrawElements
glLinkProgram
glGetProgramInfoLog
glGetProgramiv
glGetShaderInfoLog
glGetShaderiv
glGetUniformLocation
glShaderSource
glUniformMatrix4fv
glVertexAttribPointer
"""

consts = """
GL_COLOR_BUFFER_BIT
GL_COMPILE_STATUS
GL_FLOAT
GL_FRAGMENT_SHADER
GL_INFO_LOG_LENGTH
GL_LINK_STATUS
GL_TRIANGLES
GL_UNSIGNED_INT
GL_VERTEX_SHADER
"""

overrides = """
glShaderSource :: (int, int, [str], Maybe([int])) -> void
"""
