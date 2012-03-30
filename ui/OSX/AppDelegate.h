#import <Cocoa/Cocoa.h>

@class Viewport;

@interface AppDelegate : NSObject <NSApplicationDelegate, NSWindowDelegate> {
    NSWindow *window;
    Viewport *viewport;
}

@property (assign) IBOutlet NSWindow *window;
@property (assign) IBOutlet Viewport *viewport;

@end
