#import "AppDelegate.h"
#import "ViewController.h"
#import "control.h"
#import "platform.h"

@implementation AppDelegate

@synthesize window = _window;
@synthesize viewController = _viewController;

- (BOOL)application:(UIApplication *)application didFinishLaunchingWithOptions:(NSDictionary *)launchOptions
{
    self.window = [[[UIWindow alloc] initWithFrame:[[UIScreen mainScreen] bounds]] autorelease];
    self.viewController = [[[ViewController alloc] init] autorelease];
    self.window.rootViewController = self.viewController;
    [self.window makeKeyAndVisible];
    control_setup();
    return YES;
}

- (void)applicationWillTerminate:(UIApplication *)application
{
    control_shutdown();
}

- (void)dealloc
{
    [_window release];
    [_viewController release];
    [super dealloc];
}

@end