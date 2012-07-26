glClear = cimport('glClear', 'int -> void')
glClearColor = cimport('glClearColor', '(float, float, float, float) -> void')
glUniformMatrix4fv = cimport('glUniformMatrix4fv',
        '(int, int, bool, [float]) -> void')

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

GL_COLOR_BUFFER_BIT = 16384

@annot('void -> void')
def render_editor():
    glClear(GL_COLOR_BUFFER_BIT)

# vi: set sw=4 ts=4 sts=4 tw=79 ai et nocindent:
