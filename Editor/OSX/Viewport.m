#import "Viewport.h"

#include "Editor_visual.h"

@implementation Viewport

static float viewX = 0, viewY = 0;

- (void)prepareOpenGL
{
    [super prepareOpenGL];
    GLint zeroOpacity = 0;
    [self.openGLContext setValues:&zeroOpacity forParameter:NSOpenGLCPSurfaceOpacity];

    setup_editor();
    set_view_pos(viewX, viewY);
}

- (BOOL)isOpaque
{
    return NO;
}

- (void)reshape
{
    [super reshape];
    set_view_size(self.frame.size.width, self.frame.size.height);
}

- (void)drawRect:(NSRect)dirtyRect
{
    render_editor();
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
    set_view_pos(viewX, viewY);
    self.needsDisplay = YES;
}

@end
