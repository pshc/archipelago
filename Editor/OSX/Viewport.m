#import "Viewport.h"

#include "Editor_gl.h"

@implementation Viewport

- (void)prepareOpenGL
{
    [super prepareOpenGL];
    GLint zeroOpacity = 0;
    [self.openGLContext setValues:&zeroOpacity forParameter:NSOpenGLCPSurfaceOpacity];

    setup_editor();
}

- (BOOL)isOpaque
{
    return NO;
}

- (void)reshape
{
    [super reshape];
}

- (void)drawRect:(NSRect)dirtyRect
{
    // TODO: render
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

    // TODO: adjust view pos
    self.needsDisplay = YES;
}

@end
