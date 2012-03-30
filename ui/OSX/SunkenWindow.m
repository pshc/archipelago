#import "SunkenWindow.h"

#define PADDING 75

@implementation SunkenWindow

- (id)initWithContentRect:(NSRect)contentRect styleMask:(NSUInteger)aStyle backing:(NSBackingStoreType)bufferingType defer:(BOOL)flag
{
    self = [super initWithContentRect:contentRect styleMask:NSBorderlessWindowMask backing:bufferingType defer:flag];
    if (self) {
        self.opaque = NO;
        self.backgroundColor = [NSColor colorWithDeviceRed:1 green:0 blue:0 alpha:0.5];
    }
    return self;
}

- (BOOL)canBecomeKeyWindow
{
    return YES;
}

- (void)mouseDown:(NSEvent *)theEvent
{
    CGEventRef originalEvent = theEvent.CGEvent;

    self.ignoresMouseEvents = YES;
    BOOL nope = NO;
    [self performSelector:@selector(setIgnoresMouseEvents:) withObject:[NSValue valueWithBytes:&nope objCType:@encode(BOOL)] afterDelay:0.1];

    CGEventSourceRef source = CGEventCreateSourceFromEvent(originalEvent);
    CGMouseButton mouseButton = (CGMouseButton) CGEventGetIntegerValueField(originalEvent, kCGMouseEventButtonNumber);
    CGEventRef newEvent = CGEventCreateMouseEvent(source, CGEventGetType(originalEvent), CGEventGetLocation(originalEvent), mouseButton);
    CGEventPost(kCGHIDEventTap, newEvent);
    CFRelease(newEvent);
    CFRelease(source);
}

- (NSRect)contentRectForFrameRect:(NSRect)frameRect
{
    frameRect.origin = NSZeroPoint;
    return NSInsetRect(frameRect, PADDING, PADDING);
}

+ (NSRect)frameRectForContentRect:(NSRect)cRect styleMask:(NSUInteger)aStyle
{
    return NSInsetRect(cRect, -PADDING, -PADDING);
}

- (void)setContentView:(NSView *)aView
{
    if ([childContentView isEqualTo:aView]) {
        return;
    }

    NSRect bounds = {NSZeroPoint, self.frame.size};
    SunkenWindowFrameView *frameView = [super contentView];
    if (!frameView) {
        frameView = [[SunkenWindowFrameView alloc] initWithFrame:bounds];
        [super setContentView:frameView];

        NSButton *closeButton = [NSWindow standardWindowButton:NSWindowCloseButton forStyleMask:NSTitledWindowMask];
        NSRect buttonFrame = closeButton.frame;
        buttonFrame.origin = NSMakePoint(0, bounds.size.height - buttonFrame.size.height);
        closeButton.frame = buttonFrame;
        [frameView addSubview:closeButton];

        [frameView release];
    }

    if (childContentView)
    {
        [childContentView removeFromSuperview];
    }
    childContentView = aView;
    childContentView.frame = [self contentRectForFrameRect:bounds];
    childContentView.autoresizingMask = NSViewWidthSizable | NSViewHeightSizable;
    [frameView addSubview:childContentView];
}

@end

@implementation SunkenWindowFrameView



@end