#import <Foundation/Foundation.h>

@interface SunkenWindow : NSWindow
{
    NSView *childContentView;
    BOOL ignoreNextEvent;
}

@end

@interface SunkenWindowFrameView : NSView

@end
