#include <stdio.h>
#include <stdlib.h>
#include "platform.h"
#include "visual.h"

// Compile static uniform tables
#include "uniforms.h"
#undef UNIFORMS_H
#define UNIFORM_SPEC(spec) struct spec spec; const char * const _spec_##spec[] =
#define UNIFORM(name) #name,
#include "uniforms.h"

static float proj_matrix[16];

static vec2 cur_pos = {0, 0};

void set_node_pos(vec2 pos) {
    cur_pos = pos;
}

void set_view_pos(vec2 pos) {
    float mv_matrix[16] = {
        1, 0, 0, 0,
        0, 1, 0, 0,
        0, 0, 1, 0,
        -pos.x, -pos.y, 0, 1,
    };
    glUniformMatrix4fv(uniform.modelViewMatrix, 1, GL_FALSE, mv_matrix);
}

void set_view_size(struct size size) {
    int i;
    for (i = 0; i < 16; i++)
        proj_matrix[i] = 0;
    proj_matrix[0] = 2.0f / size.width;
    proj_matrix[5] = -2.0f / size.height;
    proj_matrix[10] = -1.0f;
    proj_matrix[12] = -1.0f;
    proj_matrix[13] = 1.0f;
    proj_matrix[15] = 1.0f;
    glUniformMatrix4fv(uniform.projectionMatrix, 1, GL_FALSE, proj_matrix);
}

static int compile_shader(GLenum kind, const char *name, const char *ext) {
    char *src = read_shader(name, ext);
    if (!src)
        return 0;
    
    int shader = glCreateShader(kind);
    const char **source = (const char **) &src;
    glShaderSource(shader, 1, source, NULL);
    free(src);
    
    glCompileShader(shader);
    GLint log_len;
    glGetShaderiv(shader, GL_INFO_LOG_LENGTH, &log_len);
    if (log_len > 0) {
        char *log = malloc(log_len);
        glGetShaderInfoLog(shader, log_len, &log_len, log);
        printf("Shader compile log:\n%s", log);
        free(log);
    }
    
    int status;
    glGetShaderiv(shader, GL_COMPILE_STATUS, &status);
    if (!status) {
        glDeleteShader(shader);
        return 0;
    }
    
    return shader;
}

static int link_program(int program) {
    glLinkProgram(program);
    
    GLint log_len;
    glGetProgramiv(program, GL_INFO_LOG_LENGTH, &log_len);
    if (log_len > 0) {
        char *log = malloc(log_len);
        glGetProgramInfoLog(program, log_len, &log_len, log);
        printf("Program link log:\n%s", log);
        free(log);
    }
    
    int status;
    glGetProgramiv(program, GL_LINK_STATUS, &status);
    return status;
}

int _load_shader(const char *name, void *uniforms, const char * const *spec, size_t uniform_count) {
    GLuint vertShader, fragShader;
    int program;
    size_t i;
    
    vertShader = compile_shader(GL_VERTEX_SHADER, name, "vsh");
    if (!vertShader)
        return 0;

    fragShader = compile_shader(GL_FRAGMENT_SHADER, name, "fsh");
    if (!fragShader) {
        glDeleteShader(vertShader);
        return 0;
    }
    
    program = glCreateProgram();
    glAttachShader(program, vertShader);
    glAttachShader(program, fragShader);
    
    // before linking
    glBindAttribLocation(program, ATTRIB_POS, "position");
    glBindAttribLocation(program, ATTRIB_UV, "texCoord0");
    
    int linked = link_program(program);
    if (linked) {
        unsigned int *indices = uniforms;
        for (i = 0; i < uniform_count; i++)
            indices[i] = glGetUniformLocation(program, spec[i]);
    }
    glDetachShader(program, vertShader);
    glDetachShader(program, fragShader);
    glDeleteShader(vertShader);
    glDeleteShader(fragShader);
    if (!linked) {
        glDeleteProgram(program);
        program = 0;
    }
    return program;
}

void unload_shader(int program) {
    glDeleteProgram(program);
}

struct rect_data {
    vec2 pos;
    struct pack_pos uv;
};

static void render_rects(struct rect_data *rects) {
    // VBOs later
    static GLubyte indices[] = {0, 1, 2, 0, 2, 3};
    glVertexAttribPointer(ATTRIB_POS, 2, GL_FLOAT, GL_FALSE, sizeof *rects, &rects[0].pos);
    glEnableVertexAttribArray(ATTRIB_POS);
    glVertexAttribPointer(ATTRIB_UV, 2, GL_UNSIGNED_SHORT, GL_FALSE, sizeof *rects, &rects[0].uv);
    glEnableVertexAttribArray(ATTRIB_UV);
    glDrawElements(GL_TRIANGLES, sizeof indices / sizeof *indices, GL_UNSIGNED_BYTE, indices);
}

void render_quad(struct size size, vec2 offset, struct pack_pos uv, struct size sprite) {
    float x = offset.x + cur_pos.x, y = offset.y + cur_pos.y;
    unsigned short u = uv.x + sprite.width, v = uv.y + sprite.height;
    unsigned short r = size.width + x, b = size.height + y;
    struct rect_data points[4] = {
        {{x, y}, uv},
        {{r, y}, {u, uv.y}},
        {{r, b}, {u, v}},
        {{x, b}, {uv.x, v}},
    };
    render_rects(points);
}
