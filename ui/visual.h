#ifndef VISUAL_H
#define VISUAL_H

typedef struct {
    float x, y;
} vec2;

struct size {
    unsigned short width, height;
};

struct pack_pos {
    unsigned short x, y;
};

enum { ATTRIB_POS, ATTRIB_UV };

#define load_shader(vsh, fsh, uniforms) _load_shader(vsh, fsh, &(uniforms), (_spec_##uniforms), sizeof(struct uniforms) / sizeof(unsigned int))

void unload_shader(int);
void set_view_pos(vec2);
void set_view_size(struct size);
void set_node_pos(vec2);
void render_quad(struct size size, vec2 offset, struct pack_pos uv, struct size sprite_size);

int _load_shader(const char *, const char *, void *, const char * const *, size_t);

#endif /* VISUAL_H */