#import "Viewport.h"

#include "Editor_visual.h"

@interface Viewport ()
{
    void *VISUAL_ENV;
    float viewX, viewY;
}
@end

@implementation Viewport

- (void)prepareOpenGL
{
    [super prepareOpenGL];
    GLint zeroOpacity = 0;
    [self.openGLContext setValues:&zeroOpacity forParameter:NSOpenGLCPSurfaceOpacity];

    VISUAL_ENV = setup_editor();
    if (!load_shader(VISUAL_ENV))
        NSAssert(NO, @"Exiting due to missing shader.");
    set_view_pos(viewX, viewY, VISUAL_ENV);
    NSLog(@"Preparations complete.");
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

- (void)dealloc {
    cleanup_editor(VISUAL_ENV);
}

@end
