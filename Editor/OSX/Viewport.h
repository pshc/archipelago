#import <Cocoa/Cocoa.h>

@interface Viewport : NSOpenGLView
{
    void *VISUAL_ENV;
    float viewX, viewY;
}
@end
