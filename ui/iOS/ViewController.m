#import "ViewController.h"
#import "edit.h"

@interface ViewController () {
    BOOL isEditorLoaded;
}
@property (strong, nonatomic) EAGLContext *context;
@property (strong, nonatomic) GLKBaseEffect *effect;

@end

@implementation ViewController

@synthesize context = _context;
@synthesize effect = _effect;

- (void)viewDidLoad
{
    [super viewDidLoad];
    
    self.context = [[[EAGLContext alloc] initWithAPI:kEAGLRenderingAPIOpenGLES2] autorelease];

    if (!self.context) {
        NSLog(@"Failed to create ES context");
    }

    CGRect frame = [[UIScreen mainScreen] applicationFrame];
    GLKView *view = [[GLKView alloc] initWithFrame:frame context:self.context];
    view.autoresizingMask = UIViewAutoresizingFlexibleHeight | UIViewAutoresizingFlexibleWidth;
    self.view = view;
    view.drawableDepthFormat = GLKViewDrawableDepthFormat24;
    [view release];

    [EAGLContext setCurrentContext:self.context];
    create_editor();
    isEditorLoaded = YES;
}

- (void)viewDidUnload
{    
    [super viewDidUnload];

    if (isEditorLoaded) {
        destroy_editor();
        isEditorLoaded = NO;
    }
    
    if ([EAGLContext currentContext] == self.context) {
        [EAGLContext setCurrentContext:nil];
    }
	self.context = nil;
    self.view = nil;
}

- (void)dealloc
{
    if (isEditorLoaded) {
        destroy_editor();
        isEditorLoaded = NO;
    }
    [_context release];
    [_effect release];
    [super dealloc];
}

- (BOOL)shouldAutorotateToInterfaceOrientation:(UIInterfaceOrientation)interfaceOrientation
{
    if ([[UIDevice currentDevice] userInterfaceIdiom] == UIUserInterfaceIdiomPhone) {
        return (interfaceOrientation != UIInterfaceOrientationPortraitUpsideDown);
    } else {
        return YES;
    }
}

#pragma mark - GLKView and GLKViewController delegate methods

- (void)update
{
    //float aspect = fabsf(self.view.bounds.size.width / self.view.bounds.size.height);
    //_rotation += self.timeSinceLastUpdate * 0.5f;
}

- (void)glkView:(GLKView *)view drawInRect:(CGRect)rect
{
    render_editor();
}

@end
