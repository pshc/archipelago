#import "AppDelegate.h"
#import "Viewport.h"

@implementation AppDelegate

@synthesize window;
@synthesize viewport;

- (void)applicationDidFinishLaunching:(NSNotification *)aNotification
{
    viewport.needsDisplay = YES;
}

@end
