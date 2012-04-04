#include <math.h>
#include <stdlib.h>
#include "platform.h"
#include "texture.h"
#include "uniforms.h"
#include "util.h"

#ifdef __IPHONE_OS_VERSION_MIN_REQUIRED
# include <CoreText/CoreText.h>
# include <CoreGraphics/CoreGraphics.h>
#else
# include <ApplicationServices/ApplicationServices.h>
#endif

/* TEXTURE ATLAS */

struct atlas_cell {
    struct size size;
};

struct atlas_row {
    unsigned short height, width_available;
    struct list *cells;
};

static GLuint atlas_texture = 0;
static const struct size atlas_size = {512, 512};
static struct list *atlas_rows = NULL;

static CGColorSpaceRef color_space_rgb = NULL;

void setup_texture(void) {
    glGenTextures(1, &atlas_texture);
    glBindTexture(GL_TEXTURE_2D, atlas_texture);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MIN_FILTER, GL_NEAREST);
    glTexParameteri(GL_TEXTURE_2D, GL_TEXTURE_MAG_FILTER, GL_NEAREST);
    glTexImage2D(GL_TEXTURE_2D, 0, GL_RGBA, (GLsizei) atlas_size.width, (GLsizei) atlas_size.height, 0, GL_RGBA, GL_UNSIGNED_BYTE, NULL);
    atlas_rows = nope();

    glUniform1i(uniform.atlas, 0);
    glUniform2f(uniform.invAtlasSize, 1.0f / atlas_size.width, 1.0f / atlas_size.height);
}

static void destroy_row(struct list *row) {
    free_list_by(row, &free);
}

void destroy_texture(void) {
    glDeleteTextures(1, &atlas_texture);
    free_list_by(atlas_rows, &destroy_row);
    atlas_rows = NULL;
}

static void pack_cell(struct size size, unsigned short y, struct atlas_row *row, struct pack_pos *dest) {
    dest->x = atlas_size.width - row->width_available;
    dest->y = y;
    row->width_available -= size.width;
    struct atlas_cell *new_cell = malloc(sizeof *new_cell);
    new_cell->size = size;
    row->cells = cons(new_cell, row->cells);
}

static int pack_add_rect(struct size size, struct pack_pos *dest) {
    struct atlas_row *row, *large_row = NULL;
    struct list *cur_row = atlas_rows;
    unsigned short w = size.width, h = size.height, rh, y = 0;
    unsigned short large_y, large_height = 0;
    
    for (; IS_CONS(cur_row); y += row->height, cur_row = cur_row->next) {
        row = cur_row->val;
        rh = row->height;
        if (h > rh || w > row->width_available)
            continue;
        if (h < rh/2) {
            // too short for this row, but keep as an option
            if (!large_height || large_height > h) {
                large_row = cur_row->val;
                large_y = y;
                large_height = h;
            }
            continue;
        }
        pack_cell(size, y, row, dest);
        return 1;
    }
    if (y + h > atlas_size.height) {
        if (large_row) {
            pack_cell(size, large_y, large_row, dest);
            return 1;
        }
        return 0;
    }
    /* make new row */
    cur_row->next = nope();
    row = malloc(sizeof *row);
    cur_row->val = row;
    row->width_available = atlas_size.width;
    row->height = h;
    row->cells = nope();
    pack_cell(size, y, row, dest);
    return 1;
}

void render_texture_atlas(void) {
    /*
    glBindTexture(GL_TEXTURE_2D, atlas_texture);
    int w = atlas_size.width, h = atlas_size.height;
    glColor4f(1, 1, 1, 1);
    glEnable(GL_TEXTURE_2D);
    glBegin(GL_QUADS);
    glTexCoord2f(0, 0); glVertex2i(0, 0);
    glTexCoord2f(1, 0); glVertex2i(w, 0);
    glTexCoord2f(1, 1); glVertex2i(w, h);
    glTexCoord2f(0, 1); glVertex2i(0, h);
    glEnd();
     */
}

static void free_pack_row(struct atlas_row *row) {
    free_list(row->cells);
}

static void destroy_texture_atlas(void) {
    free_list_by(atlas_rows, &free_pack_row);
}

/* TEXT TEXTURES */

struct rasterized_text *create_rasterized_text(const char *input_text) {
    CTFontRef font = CTFontCreateWithName(CFSTR("Helvetica"), 40, NULL);
    /* for italics etc, use CTFontCreateCopyWithSymbolicTraits */

    if (!color_space_rgb) {
        color_space_rgb = CGColorSpaceCreateDeviceRGB();
    }
    CGFloat white_rgba[] = {1, 1, 1, 1};
    CGColorRef white_color = CGColorCreate(color_space_rgb, white_rgba);

    const void *keys[] = {kCTFontAttributeName, kCTForegroundColorAttributeName};
    const void *values[] = {font, white_color};
    CFDictionaryRef attrs = CFDictionaryCreate(kCFAllocatorDefault, keys, values, sizeof values / sizeof *values, &kCFTypeDictionaryKeyCallBacks, &kCFTypeDictionaryValueCallBacks);
    CGColorRelease(white_color);
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
    CGContextRef bitmap = CGBitmapContextCreate(buf, width, height, 8, row, color_space_rgb, kCGImageAlphaPremultipliedLast | kCGBitmapByteOrder32Host);

    CGFloat back_rgba[] = {1, 1, 1, 0};
    CGColorRef backColor = CGColorCreate(color_space_rgb, back_rgba);
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
    
    struct pack_pos atlas_pos;
    if (!pack_add_rect(metrics.size, &atlas_pos)) {
        destroy_rasterized_text(rasterized);
        return NULL;
    }
    
    glBindTexture(GL_TEXTURE_2D, atlas_texture);
    glTexSubImage2D(GL_TEXTURE_2D, 0, atlas_pos.x, atlas_pos.y, (GLsizei) metrics.size.width, (GLsizei) metrics.size.height, GL_RGBA, GL_UNSIGNED_BYTE, rasterized->buf);
    destroy_rasterized_text(rasterized);
    
    struct text_texture *texture = malloc(sizeof *texture);
    if (!texture)
    {
        /* XXX: pack_del_rect() */
        return NULL;
    }
    
    texture->metrics = metrics;
    texture->pos = atlas_pos;

    return texture;
}

void render_text_texture(struct text_texture *text) {
    struct text_metrics m = text->metrics;
    
    /*
    glColor4f(0.5, 0.5, 0.5, 1);
    glDisable(GL_TEXTURE_2D);
    glBegin(GL_LINES);
    glVertex2i(0, 0);
    glVertex2i(m.size.width, 0);
    glEnd();
     */
    
    glBindTexture(GL_TEXTURE_2D, atlas_texture);
    glEnable(GL_TEXTURE_2D);
    vec2 offset = {0, -m.ascent};
    render_quad(m.size, offset, text->pos, m.size);
}

void destroy_text_texture(struct text_texture *text) {
    /* XXX: pack_del_rect() */
    free(text);
}
