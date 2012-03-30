#ifndef TEXTURE_H
#define TEXTURE_H

#include <stdint.h>
#include <sys/types.h>
#include "visual.h"

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
    struct pack_pos pos;
};

void setup_texture(void);
void destroy_texture(void);

struct rasterized_text *create_rasterized_text(const char *);
void destroy_rasterized_text(struct rasterized_text *);

struct text_texture *create_text_texture(const char *);
void render_text_texture(struct text_texture *text);
void destroy_text_texture(struct text_texture *);

void render_texture_atlas(void);

#endif /* TEXTURE_H */
