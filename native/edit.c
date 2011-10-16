#include <ApplicationServices/ApplicationServices.h>
#include <OpenGL/gl.h>
#include "control.h"
#include "edit.h"
#include "serial.h"
#include "util.h"

struct editor *editor = NULL;

static void render_cached_text(const char *);

void create_editor(void) {
    editor = calloc(1, sizeof *editor);

    glClearColor(0, 0, 0, 0.5);
    glEnable(GL_BLEND);
    glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

    editor->text_cache = new_map(&strcmp);

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
    glTexImage2D(GL_TEXTURE_2D, 0, GL_LUMINANCE8, 16, 16, 0, GL_LUMINANCE, GL_UNSIGNED_BYTE, pattern);
    free(pattern);
    editor->background_texture = background;
}

void resize_editor(struct size size) {
    editor->view_size = size;

    glMatrixMode(GL_PROJECTION);
    glLoadIdentity();
    glOrtho(0, size.width, size.height, 0, -1, 1);
    glViewport(0, 0, size.width, size.height);
    glMatrixMode(GL_MODELVIEW);
}

static struct position layout_pos;
#define LO_LINE_HEIGHT 50
#define LO_INDENT 50

struct layout_node {
    struct position pos;
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
static void layout_close(void) {
    layout_pos.x -= LO_INDENT;
}
static void layout_ref(intptr_t *object) {
    layout_pos.y += LO_LINE_HEIGHT;
    struct layout_node *node = malloc(sizeof *node);
    node->pos = layout_pos;
    node->kind = LAYOUT_REF;
    node->obj = object;
    editor->layout = cons(node, editor->layout);
}

static void layout_editor(void) {
    layout_pos.x = layout_pos.y = 0;
    editor->layout = nope();
    editor->layout_map = new_map(NULL);

    struct walker walker = {&layout_int, NULL, &layout_open, &layout_close, &layout_ref};
    walk_object(editor->module->root, editor->module->root_type, &walker);
}

void editor_set_module(struct module *module) {
    editor->module = module;
    layout_editor();
}

static void render_arrow(struct position a, struct position b) {
    glBindTexture(GL_TEXTURE_2D, 0);
    glBegin(GL_LINES);
    glVertex2i(a.x, a.y);
    glVertex2i(b.x, b.y);
    glEnd();
}

static void render_layout_node(struct layout_node *node) {

    if (node->kind == LAYOUT_REF) {
        struct layout_node *dest = map_get(editor->layout_map, node->obj);
        render_arrow(node->pos, dest->pos);
        return;
    }

    glPushMatrix();
    glTranslatef(node->pos.x, node->pos.y, 0);
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
            struct ctor *ctor = node->context;
            render_cached_text(ctor->name);
            break;
        }
        default:
            fail("Unexpected layout node %d", node->kind);
    }
    glPopMatrix();
}

void render_editor(void) {
    glLoadIdentity();

    // background
    //glClear(GL_COLOR_BUFFER_BIT);
    glColor4f(1, 1, 1, 1);
    glEnable(GL_TEXTURE_2D);
    glBindTexture(GL_TEXTURE_2D, editor->background_texture);
    struct position pos = editor->view_pos;
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
    glTranslatef(0, -editor->view_pos.y, 0);
    glColor4f(0.5, 0.5, 0.5, 1);
    glDisable(GL_TEXTURE_2D);
    glBegin(GL_LINES);
    glVertex2i(-100, 0);
    glVertex2i(1000, 0);
    glVertex2i(0, -100);
    glVertex2i(0, 1000);
    glEnd();

    if (editor->module) {
        struct list *pos;
        for (pos = editor->layout; IS_CONS(pos); pos = pos->next)
            render_layout_node(pos->val);
    }

    // flush done by platform
}

void destroy_editor(void) {
    glDeleteTextures(1, &editor->background_texture);
    free(editor);
    editor = NULL;
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
    render_text_texture(texture);
}

/* TEXT TEXTURES */

struct rasterized_text *create_rasterized_text(const char *input_text) {
    CTFontRef font = CTFontCreateWithName(CFSTR("Helvetica"), 40, NULL);
    /* for italics etc, use CTFontCreateCopyWithSymbolicTraits */
    CGColorRef color = CGColorCreateGenericRGB(1, 1, 1, 1);

    const void *keys[] = {kCTFontAttributeName, kCTForegroundColorAttributeName};
    const void *values[] = {font, color};
    CFDictionaryRef attrs = CFDictionaryCreate(kCFAllocatorDefault, keys, values, sizeof values / sizeof *values, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);
    CGColorRelease(color);
    CFRelease(font);

    CFStringRef unattributed = CFStringCreateWithCString(kCFAllocatorDefault, input_text, kCFStringEncodingUTF8);
    CFAttributedStringRef attributed = CFAttributedStringCreate(kCFAllocatorDefault, unattributed, attrs);
    CFRelease(unattributed);
    CFRelease(attrs);

    CTLineRef line = CTLineCreateWithAttributedString(attributed);
    CFRelease(attributed);
    if (!line)
        return NULL;

    CGFloat ascent, descent, leading;
    double w = CTLineGetTypographicBounds(line, &ascent, &descent, &leading);

    size_t width = (size_t) ceil(w);
    size_t height = (size_t) ceil(ascent + descent);
    size_t row = width * 4;

    void *buf = calloc(height, row);
    if (!buf)
    {
        CFRelease(line);
        return NULL;
    }
    CGColorSpaceRef rgb = CGColorSpaceCreateDeviceRGB();
    CGContextRef bitmap = CGBitmapContextCreate(buf, width, height, 8, row, rgb, kCGImageAlphaPremultipliedLast | kCGBitmapByteOrder32Host);
    CGColorSpaceRelease(rgb);

    CGColorRef backColor = CGColorCreateGenericRGB(1, 1, 1, 0);
    CGContextSetFillColorWithColor(bitmap, backColor);
    CGColorRelease(backColor);

    CGRect rect = {CGPointZero, {width, height}};
    CGContextFillRect(bitmap, rect);

    CGContextSetTextPosition(bitmap, 0, descent);
    CTLineDraw(line, bitmap);
    CGContextFlush(bitmap);

    CGContextRelease(bitmap);
    CFRelease(line);

    struct rasterized_text *out = malloc(sizeof *out);
    if (!out)
    {
        free(buf);
        return NULL;
    }

    out->metrics.size.width = (unsigned short) width;
    out->metrics.size.height = (unsigned short) height;
    out->metrics.ascent = ascent;
    out->metrics.descent = descent;
    out->stride = row;
    out->buf = buf;

    return out;
}

void destroy_rasterized_text(struct rasterized_text *text) {
    free(text->buf);
    free(text);
}

struct text_texture *create_text_texture(const char *text) {
    struct rasterized_text *rasterized = create_rasterized_text(text);
    if (!rasterized)
        return NULL;

    struct text_metrics metrics = rasterized->metrics;

    GLuint index;
    glGenTextures(1, &index);
    glBindTexture(GL_TEXTURE_2D, index);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
    glTexImage2D(GL_TEXTURE_2D, 0, 4, (GLsizei) metrics.size.width, (GLsizei) metrics.size.height, 0, GL_RGBA, GL_UNSIGNED_BYTE, rasterized->buf);
    destroy_rasterized_text(rasterized);

    struct text_texture *texture = malloc(sizeof *texture);
    if (!texture)
    {
        glDeleteTextures(1, &index);
        return NULL;
    }

    texture->metrics = metrics;
    texture->texture = index;

    return texture;
}

void render_text_texture(struct text_texture *text) {
    struct text_metrics m = text->metrics;
    int w = m.size.width, h = m.size.height;
    int a = m.ascent;
    
    glColor4f(0.5, 0.5, 0.5, 1);
    glDisable(GL_TEXTURE_2D);
    glBegin(GL_LINES);
    glVertex2i(0, 0);
    glVertex2i(w, 0);
    glEnd();
    
    glBindTexture(GL_TEXTURE_2D, text->texture);
    glColor4f(1, 1, 1, 1);
    glEnable(GL_TEXTURE_2D);
    glBegin(GL_QUADS);
    glTexCoord2f(0, 0); glVertex2i(0, -a);
    glTexCoord2f(1, 0); glVertex2i(w, -a);
    glTexCoord2f(1, 1); glVertex2i(w, h-a);
    glTexCoord2f(0, 1); glVertex2i(0, h-a);
    glEnd();
}

void destroy_text_texture(struct text_texture *text) {
    glDeleteTextures(1, &text->texture);
    free(text);
}