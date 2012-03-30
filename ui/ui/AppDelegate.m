#import "AppDelegate.h"
#import "Viewport.h"
#import <objc/runtime.h>
#import "control.h"
#import "platform.h"

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
    viewport.needsDisplay = YES;
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

char *read_resource(const char *name)
{
    // Man is this dumb. So much unnecessary glue
    NSArray *bits = [[NSString stringWithCString:name encoding:NSUTF8StringEncoding] componentsSeparatedByString:@"."];
    if ([bits count] != 2)
    {
        NSCAssert(FALSE, @"Couldn't figure out extension of %s", name);
        return NULL;
    }
    NSString *path = [[NSBundle mainBundle] pathForResource:[bits objectAtIndex:0] ofType:[bits objectAtIndex:1]];
    if (!path)
    {
        NSCAssert(FALSE, @"Couldn't get path for %s", name);
        return NULL;
    }
    NSError *error = nil;
    NSData *contents = [[NSData alloc] initWithContentsOfFile:path options:0 error:&error];
    if (!contents || error)
    {
        NSCAssert(FALSE, @"Couldn't read %s: %@", name, error);
        [contents release];
        return NULL;
    }
    NSUInteger len = [contents length];
    char *buf = malloc(len + 1);
    if (!buf)
    {
        [contents release];
        return NULL;
    }
    [contents getBytes:buf length:len];
    [contents release];
    buf[len] = '\0';
    return buf;
}