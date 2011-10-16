#import "AppDelegate.h"
#import "Viewport.h"
#import <objc/runtime.h>
#import "control.h"

@interface NSWindow ()
- (void)drawRectOriginal:(NSRect)rect;
@end

@interface StyledWindow : NSWindow
@end

@implementation StyledWindow

+ (void)installCustomDrawRectIntoWindow:(NSWindow *)window
{
    id class = [[[window contentView] superview] class];
    
    Method m0 = class_getInstanceMethod([StyledWindow class], @selector(drawWindowFrameRect:));
    class_addMethod(class, @selector(drawRectOriginal:), method_getImplementation(m0), method_getTypeEncoding(m0));
    
    Method m1 = class_getInstanceMethod(class, @selector(drawRect:));
    Method m2 = class_getInstanceMethod(class, @selector(drawRectOriginal:));
    method_exchangeImplementations(m1, m2);
}

- (void)drawWindowFrameRect:(NSRect)dirtyRect
{
    //[self drawRectOriginal:dirtyRect];

    NSRect windowRect = {NSZeroPoint, self.frame.size};
    CGFloat diff = windowRect.size.height - 22 - dirtyRect.origin.y;
    if (diff > 0)
    {
        dirtyRect.origin.y += diff;
        dirtyRect.size.height -= diff;
    }
    float cornerRadius = 4;
    [[NSBezierPath bezierPathWithRect:dirtyRect] addClip];
    [[NSBezierPath bezierPathWithRoundedRect:windowRect xRadius:cornerRadius yRadius:cornerRadius] addClip];

    [[NSColor blackColor] setFill];
    NSRectFill(dirtyRect);
}

@end

@implementation AppDelegate

@synthesize window;
@synthesize viewport;

- (void)applicationDidFinishLaunching:(NSNotification *)aNotification
{
    if ([window class] == [NSWindow class])
    {
        [StyledWindow installCustomDrawRectIntoWindow:window];
    }
    control_setup();
}

- (void)applicationWillTerminate:(NSNotification *)notification
{
    control_shutdown();
}

- (BOOL)windowShouldClose:(id)sender
{
    [[NSApplication sharedApplication] terminate:nil];
    return YES;
}

@end
