#ifndef EDIT_H
#define EDIT_H

#include <stdint.h>
#include <sys/types.h>
#include "visual.h"

struct editor;
struct module;

extern struct editor *editor;

void create_editor(void);
void resize_editor(struct size);
void editor_set_view_pos(vec2);
void editor_set_module(struct module *);
void render_editor(void);
void destroy_editor(void);

#endif /* EDIT_H */
