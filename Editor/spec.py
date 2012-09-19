funcs = """
glAttachShader
glBindAttribLocation
glBindTexture
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
glGenTextures
glGetProgramInfoLog
glGetProgramiv
glGetShaderInfoLog
glGetShaderiv
glGetUniformLocation
glShaderSource
glTexImage2D
glTexParameteri
glUseProgram
glUniformMatrix4fv
glViewport
glVertexAttribPointer
"""

consts = """
GL_ALPHA
GL_COLOR_BUFFER_BIT
GL_COMPILE_STATUS
GL_FLOAT
GL_FRAGMENT_SHADER
GL_INFO_LOG_LENGTH
GL_LINK_STATUS
GL_NEAREST
GL_TEXTURE_2D
GL_TEXTURE_MAG_FILTER
GL_TEXTURE_MIN_FILTER
GL_TRIANGLES
GL_UNSIGNED_BYTE
GL_UNSIGNED_INT
GL_VERTEX_ARRAY
GL_VERTEX_SHADER
"""

overrides = """
glDrawElements indices :: [int]
glGenTextures textures :: [int]
glShaderSource length :: Maybe([int])
glTexImage2D pixels :: Maybe(str)
glVertexAttribPointer pointer :: [float]
"""
