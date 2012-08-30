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
glEnableClientState
glEnableVertexAttribArray
glLinkProgram
glGetProgramInfoLog
glGetProgramiv
glGetShaderInfoLog
glGetShaderiv
glGetUniformLocation
glShaderSource
glUseProgram
glUniformMatrix4fv
glViewport
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
GL_VERTEX_ARRAY
GL_VERTEX_SHADER
"""

overrides = """
glShaderSource :: (int, int, [str], Maybe([int])) -> void
"""
