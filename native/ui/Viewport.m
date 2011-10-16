#import <OpenGL/gl.h>
#import "Viewport.h"
#import "edit.h"
#import "serial.h"

@interface Viewport ()
{
    struct position pointerOrigin, scrollOrigin;
}
@end

@implementation Viewport

- (void)prepareOpenGL
{
    [super prepareOpenGL];

    GLint zeroOpacity = 0;
    [self.openGLContext setValues:&zeroOpacity forParameter:NSOpenGLCPSurfaceOpacity];

    create_editor();
}

- (BOOL)isOpaque
{
    return NO;
}

- (void)reshape
{
    [super reshape];

    struct size size = {self.frame.size.width, self.frame.size.height};
    resize_editor(size);
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

    editor->view_pos.x -= dx;
    editor->view_pos.y -= dy;
    self.needsDisplay = YES;
}

- (void)dealloc
{
    destroy_editor();
    [super dealloc];
}

@end
