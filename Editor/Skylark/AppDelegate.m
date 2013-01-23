#import "AppDelegate.h"

#import "EditorViewController.h"

@implementation AppDelegate

- (BOOL)application:(UIApplication *)application didFinishLaunchingWithOptions:(NSDictionary *)launchOptions
{
    self.window = [[UIWindow alloc] initWithFrame:[[UIScreen mainScreen] bounds]];
    self.window.rootViewController = [[EditorViewController alloc] init];
    [self.window makeKeyAndVisible];
    return YES;
}

@end
