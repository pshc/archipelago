#ifndef EDIT_H
#define EDIT_H

#include <stdint.h>
#include <sys/types.h>

struct list;
struct map;
struct module;

struct position {
    float x, y;
};

struct size {
    unsigned short width, height;
};

struct text_metrics {
    struct size size;
    short ascent, descent;
};

struct rasterized_text {
    struct text_metrics metrics;
    size_t stride;
    uint8_t *buf;
};

struct text_texture {
    struct text_metrics metrics;
    unsigned int texture;
};

struct editor {
    struct module *module;
    struct position view_pos;
    struct size view_size;
    struct map *text_cache;
    struct list *layout;
    struct map *layout_map;
    unsigned int background_texture;
};

extern struct editor *editor;

struct rasterized_text *create_rasterized_text(const char *);
void destroy_rasterized_text(struct rasterized_text *);

struct text_texture *create_text_texture(const char *);
void render_text_texture(struct text_texture *text);
void destroy_text_texture(struct text_texture *);

void create_editor(void);
void resize_editor(struct size);
void editor_set_module(struct module *);
void render_editor(void);
void destroy_editor(void);

#endif /* EDIT_H */
