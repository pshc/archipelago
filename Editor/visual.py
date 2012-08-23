from Editor.gl import *
from bedrock import *

fragmentShaderSrc = """
varying lowp vec2 uv;
uniform sampler2D atlas;

void main () {
    lowp vec4 col = texture2D(atlas, uv);
    gl_FragColor = vec4(uv, 1.0 - uv.x, col.a * (uv.y * 0.5 + 0.5));
}
"""

vertexShaderSrc = """
attribute lowp vec2 position;
attribute lowp vec2 texCoord0;

varying lowp vec2 uv;

uniform mat4 modelViewMatrix;
uniform mat4 projectionMatrix;
uniform lowp vec2 invAtlasSize;

void main() {
    uv = texCoord0 * invAtlasSize;
    gl_Position = projectionMatrix * modelViewMatrix * vec4(position,0.0,1.0);
}
"""

ATTRIB_POS = 0

Vec2 = DT('Vec2', ('x', float), ('y', float))

SceneNode = DT('SceneNode',
        ('position', Vec2))

@annot('void -> void')
def setup_editor():
    glClearColor(0.0, 0.0, 0.0, 1.0)

@annot('(float, float) -> void')
def set_view_size(width, height):
    projMat = [
        2.0 / width, 0.0, 0.0, 0.0,
        0.0, -2.0 / height, 0.0, 0.0,
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
    uniform = 1
    glUniformMatrix4fv(uniform, 1, False, mvMat)

@annot('void -> void')
def render_editor():
    glClear(GL_COLOR_BUFFER_BIT)

@annot('(str, int) -> int')
def compile_shader(src, kind):
    shader = glCreateShader(kind)
    glShaderSource(shader, 1, [src], Nothing())

    glCompileShader(shader)
    logLen = [0]
    glGetShaderiv(shader, GL_INFO_LOG_LENGTH, logLen)
    if logLen[0] > 0:
        pass # print log

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
        pass # print log

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
        pass # get uniforms
    glDetachShader(program, vertShader)
    glDetachShader(program, fragShader)
    glDeleteShader(vertShader)
    glDeleteShader(fragShader)
    if not linked:
        glDeleteProgram(program)
        program = 0
    return program

@annot('int -> void')
def unload_shader(program):
    glDeleteProgram(program)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
