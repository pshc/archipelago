#import "Viewport.h"

#include "Editor_visual.h"

@implementation Viewport

static float viewX = 0, viewY = 0;

static void* VISUAL_ENV;

- (void)prepareOpenGL
{
    [super prepareOpenGL];
    GLint zeroOpacity = 0;
    [self.openGLContext setValues:&zeroOpacity forParameter:NSOpenGLCPSurfaceOpacity];

    VISUAL_ENV = setup_editor();
    if (!load_shader(VISUAL_ENV))
        NSAssert(NO, @"Exiting due to missing shader.");
    set_view_pos(viewX, viewY, VISUAL_ENV);
}

- (BOOL)isOpaque
{
    return NO;
}

- (void)reshape
{
    [super reshape];
    set_view_size(self.frame.size.width, self.frame.size.height, VISUAL_ENV);
}

- (void)drawRect:(NSRect)dirtyRect
{
    render_editor(VISUAL_ENV);
    [self.openGLContext flushBuffer];
}

- (void)scrollWheel:(NSEvent *)theEvent
{
    CGFloat dx, dy;
    if ([theEvent respondsToSelector:@selector(hasPreciseScrollingDeltas)])
    {
        if (theEvent.hasPreciseScrollingDeltas)
        {
            dx = theEvent.scrollingDeltaX;
            dy = theEvent.scrollingDeltaY;
        }
        else
        {
            CGFloat lineHeight = 12; // or something
            dx = theEvent.scrollingDeltaX * lineHeight;
            dy = theEvent.scrollingDeltaY * lineHeight;
        }
    }
    else
    {
        dx = theEvent.deltaX;
        dy = theEvent.deltaY;
    }

    viewX -= dx;
    viewY -= dy;
    set_view_pos(viewX, viewY, VISUAL_ENV);
    self.needsDisplay = YES;
}

@end
