from Editor.gl import *
from bedrock import *

fragmentShaderSrc = """
void main () {
    gl_FragColor = vec4(1.0, 0.5, 0.0, 1.0);
}
"""

vertexShaderSrc = """
attribute vec2 position;

uniform mat4 modelViewMatrix;
uniform mat4 projectionMatrix;

void main() {
    gl_Position = projectionMatrix * modelViewMatrix * vec4(position,0.0,1.0);
}
"""

ATTRIB_POS = 0

Vec2 = DT('Vec2', ('x', float), ('y', float))

SceneNode = DT('SceneNode',
        ('position', Vec2))

@annot('(int, int) -> void')
def set_view_size(width, height):
    glViewport(0, 0, width, height)
    projMat = [
        2.0 / float(width), 0.0, 0.0, 0.0,
        0.0, -2.0 / float(height), 0.0, 0.0,
        0.0, 0.0, -1.0, 0.0,
        -1.0, 1.0, 0.0, 1.0,
    ]
    uniform = 0
    glUniformMatrix4fv(uniform, 1, False, projMat)

@annot('(float, float) -> void')
def set_view_pos(x, y):
    mvMat = [
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, 0.0,
        0.0, 0.0, 1.0, 0.0,
         -x,  -y, 0.0, 1.0,
    ]
    uniform = 4
    glUniformMatrix4fv(uniform, 1, False, mvMat)

@annot('(str, int) -> int')
def compile_shader(src, kind):
    shader = glCreateShader(kind)
    glShaderSource(shader, 1, [src], Nothing())

    glCompileShader(shader)
    logLen = [0]
    glGetShaderiv(shader, GL_INFO_LOG_LENGTH, logLen)
    if logLen[0] > 0:
        log = buffer(logLen[0])
        glGetShaderInfoLog(shader, logLen[0], logLen, log)
        print log

    status = [0]
    glGetShaderiv(shader, GL_COMPILE_STATUS, status)
    if status[0] == 0:
        glDeleteShader(shader)
        return 0

    return shader

@annot('int -> bool')
def link_program(program):
    glLinkProgram(program)

    logLen = [0]
    glGetProgramiv(program, GL_INFO_LOG_LENGTH, logLen)
    if logLen[0] > 0:
        log = buffer(logLen[0])
        glGetProgramInfoLog(program, logLen[0], logLen, log)
        print log

    status = [0]
    glGetProgramiv(program, GL_LINK_STATUS, status)
    return status[0] != 0

@annot('void -> int')
def load_shader():
    vertShader = compile_shader(vertexShaderSrc, GL_VERTEX_SHADER)
    if vertShader == 0:
        return 0
    fragShader = compile_shader(fragmentShaderSrc, GL_FRAGMENT_SHADER)
    if fragShader == 0:
        glDeleteShader(vertShader)
        return 0

    program = glCreateProgram()
    glAttachShader(program, vertShader)
    glAttachShader(program, fragShader)

    glBindAttribLocation(program, ATTRIB_POS, "position")

    linked = link_program(program)
    if linked:
        mvmat = glGetUniformLocation(program, "modelViewMatrix")
        pmat = glGetUniformLocation(program, "projectionMatrix")
        print 'mvmat %d pmat %d' % (mvmat, pmat)

    glDetachShader(program, vertShader)
    glDetachShader(program, fragShader)
    glDeleteShader(vertShader)
    glDeleteShader(fragShader)
    if not linked:
        glDeleteProgram(program)
        program = 0
    else:
        print 'using program %d' % (program,)
        glUseProgram(program)
    return program

@annot('int -> void')
def unload_shader(program):
    glDeleteProgram(program)

@annot('void -> void')
def setup_editor():
    glClearColor(0.0, 0.0, 0.0, 1.0)

    glEnableVertexAttribArray(ATTRIB_POS)
    glEnableClientState(GL_VERTEX_ARRAY)

    load_shader()

@annot('(float, float, float, float) -> void')
def render_quad(x, y, w, h):
    r = fadd(x, w)
    b = fadd(y, h)
    points = [
        x, y,
        r, y,
        r, b,
        x, b,
    ]
    indices = [0, 1, 2, 0, 2, 3]
    glVertexAttribPointer(ATTRIB_POS, 2, GL_FLOAT, False, 0, points)
    glDrawElements(GL_TRIANGLES, 6, GL_UNSIGNED_INT, indices)

@annot('void -> void')
def render_editor():
    glClear(GL_COLOR_BUFFER_BIT)
    render_quad(0.0, 0.0, 100.0, 100.0)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
