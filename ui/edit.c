#include <math.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "control.h"
#include "edit.h"
#include "serial.h"
#include "platform.h"
#include "texture.h"
#include "uniforms.h"
#include "util.h"
#include "visual.h"

struct editor {
    struct module *module;
    vec2 view_pos;
    struct size view_size;
    struct map *text_cache;
    struct list *layout;
    struct map *layout_map;
    unsigned int background_texture;

    int shader_program;
};

struct editor *editor = NULL;

void create_editor(void) {
    editor = calloc(1, sizeof *editor);

    glClearColor(0, 0, 0, 1);
    glEnable(GL_BLEND);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

    glEnableVertexAttribArray(ATTRIB_POS);
    glEnableVertexAttribArray(ATTRIB_UV);

#ifndef GL_ES_VERSION_2_0
    glEnableClientState(GL_VERTEX_ARRAY);
#endif

    unsigned int background;
    glGenTextures(1, &background);
    glBindTexture(GL_TEXTURE_2D, background);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
    uint8_t *pattern = calloc(16, 16);
    int x, y;
    for (y = 0; y < 16; y++)
        for (x = y%8; x < 16; x += 8)
            pattern[y*16 + x] = 50;
    glTexImage2D(GL_TEXTURE_2D, 0, GL_LUMINANCE, 16, 16, 0, GL_LUMINANCE, GL_UNSIGNED_BYTE, pattern);
    free(pattern);
    editor->background_texture = background;

    editor->shader_program = load_shader("shader", uniform);
    glUseProgram(editor->shader_program);
    setup_texture();

    editor->text_cache = new_map(&strcmp, &free, &destroy_rasterized_text);
}

void resize_editor(struct size size) {
    editor->view_size = size;
    glViewport(0, 0, size.width, size.height);
    glUseProgram(editor->shader_program);
    set_view_size(size);
}

void editor_move_view_pos(vec2 dir) {
    editor->view_pos.x += dir.x;
    editor->view_pos.y += dir.y;
}

static vec2 layout_pos;
#define LO_LINE_HEIGHT 25
#define LO_INDENT 25

struct layout_node {
    vec2 pos;
    enum { LAYOUT_INT, LAYOUT_OBJ, LAYOUT_REF } kind;
    intptr_t *obj;
    void *context;
};

static void layout_int(int i) {
    layout_pos.y += LO_LINE_HEIGHT;
    struct layout_node *node = malloc(sizeof *node);
    node->pos = layout_pos;
    node->pos.x += LO_INDENT;
    node->kind = LAYOUT_INT;
    node->obj = (intptr_t *) i;
    editor->layout = cons(node, editor->layout);
}
static void layout_open(intptr_t *object, struct adt *adt, struct ctor *ctor) {
    layout_pos.x += LO_INDENT;
    layout_pos.y += LO_LINE_HEIGHT;
    struct layout_node *node = malloc(sizeof *node);
    node->pos = layout_pos;
    node->kind = LAYOUT_OBJ;
    node->obj = object;
    node->context = ctor;
    editor->layout = cons(node, editor->layout);
    map_set(editor->layout_map, object, node);
}
static void layout_close(intptr_t *object) {
    layout_pos.x -= LO_INDENT;
}
static void layout_ref(intptr_t *object) {
    layout_pos.y += LO_LINE_HEIGHT;
    struct layout_node *node = malloc(sizeof *node);
    node->pos = layout_pos;
    node->pos.x += LO_INDENT;
    node->kind = LAYOUT_REF;
    node->obj = object;
    editor->layout = cons(node, editor->layout);
}

static void layout_editor(void) {
    layout_pos.x = layout_pos.y = 0;
    editor->layout = nope();
    editor->layout_map = new_map(NULL, NULL, NULL);

    struct walker walker = {&layout_int, NULL, NULL, &layout_open, &layout_close, &layout_ref};
    walk_object(editor->module->root, editor->module->root_type, &walker);
}

void editor_set_module(struct module *module) {
    editor->module = module;
    layout_editor();
}

static vec2 cubic_bezier(const vec2 v[4], float t) {
    float t2 = t*t;
    float t3 = t2*t;
    float s = 1 - t;
    float s2 = s*s;
    float s3 = s2*s;
    vec2 p = {
            s3*v[0].x + 3*s2*t*v[1].x + 3*s*t2*v[2].x + t3*v[3].x,
            s3*v[0].y + 3*s2*t*v[1].y + 3*s*t2*v[2].y + t3*v[3].y
    };
    return p;
}

static vec2 cubic_bezier_deriv(const vec2 v[4], float t) {
    float t2 = t*t;
    vec2 p = {
            3*(-t2 + 2*t - 1)*v[0].x + 3*(3*t2 - 4*t + 1)*v[1].x + 3*(-3*t2 + 2*t)*v[2].x + 3*t2*v[3].x,
            3*(-t2 + 2*t - 1)*v[0].y + 3*(3*t2 - 4*t + 1)*v[1].y + 3*(-3*t2 + 2*t)*v[2].y + 3*t2*v[3].y
    };
    return p;
}

static vec2 normalize(vec2 v) {
    float mag = sqrtf(v.x*v.x + v.y*v.y), invmag;
    if (mag) {
        invmag = 1.0/mag;
        v.x *= invmag;
        v.y *= invmag;
    }
    else {
        v.x = v.y = 0;
    }
    return v;
}

static vec2 rotate(vec2 d, float rad) {
    float c = cosf(rad), s = sinf(rad);
    // y flipped
    vec2 pos = {d.x*c + d.y*s, d.x*s - d.y*c};
    return pos;
}

static void render_arrow(vec2 a, vec2 b) {
    /*
    vec2 points[4] = {a, {0, a.y}, {0, b.y}, b};
    vec2 pos;
    float t;

    points[0].y -= LO_LINE_HEIGHT/3;
    points[3].y -= LO_LINE_HEIGHT/3;
    glBindTexture(GL_TEXTURE_2D, 0);

    pos = points[0];
    float radius = 7;
    glBegin(GL_LINE_STRIP);
    for (t = 0; t <= M_PI * 2 + 0.0001; t += M_PI/8) {
        glVertex2f(pos.x + cosf(t)*radius, pos.y - sinf(t)*radius);
    }
    glEnd();

    glBegin(GL_LINE_STRIP);
    for (t = 0; t <= 0.9001; t += 0.05) {
        pos = cubic_bezier(points, t);
        glVertex2f(pos.x, pos.y);
    }
    glEnd();

    vec2 d = cubic_bezier_deriv(points, 0.9);
    d = normalize(d);
    vec2 p1 = rotate(d, M_PI * 8/9), p2 = rotate(d, M_PI * 10/9);
    float arrow_mag = 15;
    glBegin(GL_LINES);
    glVertex2f(pos.x, pos.y);
    glVertex2f(pos.x + p1.x*arrow_mag, pos.y - p1.y*arrow_mag);
    glVertex2f(pos.x, pos.y);
    glVertex2f(pos.x + p2.x*arrow_mag, pos.y - p2.y*arrow_mag);
    glEnd();
     */
}

static const char *get_layout_obj_desc(struct layout_node *node) {
    const char *name;
    if (map_has(atom_names, node->obj))
        name = map_get(atom_names, node->obj);
    else
        name = ((struct ctor *) node->context)->name;
    return name;
}

static void render_cached_text(const char *text) {
    struct map *cache = editor->text_cache;
    struct text_texture *texture;
    if (map_has(cache, text)) {
        texture = map_get(cache, text);
    }
    else {
        texture = create_text_texture(text);
        map_set(cache, strdup(text), texture);
    }
    if (texture)
        render_text_texture(texture);
}

static void render_layout_node(struct layout_node *node) {

    struct layout_node *dest = NULL;
    if (node->kind == LAYOUT_REF) {
        if (map_has(editor->layout_map, node->obj)) {
            dest = map_get(editor->layout_map, node->obj);
            glUseProgram(0);
            render_arrow(node->pos, dest->pos);
            glUseProgram(editor->shader_program);
        }
    }

    set_node_pos(node->pos);
    switch (node->kind) {
        case LAYOUT_INT:
        {
            char buf[10];
            sprintf(buf, "%d", (int) node->obj);
            render_cached_text(buf);
            break;
        }
        case LAYOUT_OBJ:
        {
            render_cached_text(get_layout_obj_desc(node));
            break;
        }
        case LAYOUT_REF:
        {
            if (dest) {
                const char *desc = get_layout_obj_desc(dest);
                char *ref_desc = alloca(strlen(desc) + 4);
                strcpy(ref_desc, " ->");
                strcat(ref_desc, desc);
                render_cached_text(ref_desc);
            }
            else {
                render_cached_text(" ->???");
            }
            break;
        }
        default:
            fail("Unexpected layout node %d", node->kind);
    }
}

void render_editor(void) {

    glUseProgram(0);

    // background
    glClear(GL_COLOR_BUFFER_BIT);
    /*
    glColor4f(1, 1, 1, 1);
    glEnable(GL_TEXTURE_2D);
    glBindTexture(GL_TEXTURE_2D, editor->background_texture);
    vec2 pos = editor->view_pos;
    struct size size = editor->view_size;
    float y = pos.y / 16.0;
    float w = size.width / 16.0, h = size.height / 16.0;
    glBegin(GL_QUADS);
    glTexCoord2f(0, y); glVertex2i(0, 0);
    glTexCoord2f(w, y); glVertex2i(size.width, 0);
    glTexCoord2f(w, y+h); glVertex2i(size.width, size.height);
    glTexCoord2f(0, y+h); glVertex2i(0, size.height);
    glEnd();

    // origin
    glTranslatef(-editor->view_pos.x, -editor->view_pos.y, 0);
    glColor4f(0.5, 0.5, 0.5, 1);
    glDisable(GL_TEXTURE_2D);
    glBegin(GL_LINES);
    glVertex2i(-100, 0);
    glVertex2i(1000, 0);
    glVertex2i(0, -100);
    glVertex2i(0, 1000);
    glEnd();
    */

    glUseProgram(editor->shader_program);
    set_view_pos(editor->view_pos);

    if (editor->module) {
        struct list *pos;
        for (pos = editor->layout; IS_CONS(pos); pos = pos->next)
            render_layout_node(pos->val);
    }

    // flush done by platform
}

void destroy_editor(void) {
    if (editor->layout_map)
        destroy_map(editor->layout_map);
    if (editor->layout)
        free_list(editor->layout);
    destroy_map(editor->text_cache);
    glDeleteTextures(1, &editor->background_texture);
    destroy_texture();
    unload_shader(editor->shader_program);
    free(editor);
    editor = NULL;
}