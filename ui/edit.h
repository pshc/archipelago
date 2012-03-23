#ifndef EDIT_H
#define EDIT_H

#include <stdint.h>
#include <sys/types.h>

struct list;
struct map;
struct module;

typedef struct {
    float x, y;
} vec2;

struct size {
    unsigned short width, height;
};

extern struct editor *editor;

struct rasterized_text *create_rasterized_text(const char *);
void destroy_rasterized_text(struct rasterized_text *);

struct text_texture *create_text_texture(const char *);
void render_text_texture(struct text_texture *text);
void destroy_text_texture(struct text_texture *);

void create_editor(void);
void resize_editor(struct size);
void editor_move_view_pos(vec2);
void editor_set_module(struct module *);
void render_editor(void);
void destroy_editor(void);

#endif /* EDIT_H */
