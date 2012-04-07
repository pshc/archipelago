#import "ViewController.h"
#import "edit.h"

@interface ViewController () {
    BOOL isEditorLoaded;
    vec2 viewPos;
    vec2 panStart;
}
@property (strong, nonatomic) EAGLContext *context;
@property (strong, nonatomic) UIPanGestureRecognizer *panRecognizer;

@end

@implementation ViewController

@synthesize context = _context;
@synthesize panRecognizer;

- (void)viewDidLoad
{
    [super viewDidLoad];
    
    self.context = [[[EAGLContext alloc] initWithAPI:kEAGLRenderingAPIOpenGLES2] autorelease];
    [EAGLContext setCurrentContext:self.context];

    CGRect frame = [[UIScreen mainScreen] applicationFrame];
    GLKView *view = [[GLKView alloc] initWithFrame:frame context:self.context];
    view.autoresizingMask = UIViewAutoresizingFlexibleHeight | UIViewAutoresizingFlexibleWidth;
    view.drawableDepthFormat = GLKViewDrawableDepthFormat24;
    view.opaque = YES;

    self.panRecognizer = [[UIPanGestureRecognizer alloc] initWithTarget:self action:@selector(handlePan)];
    [view addGestureRecognizer:panRecognizer];
    [panRecognizer release];

    create_editor();
    struct size size = {view.bounds.size.width, view.bounds.size.height};
    resize_editor(size);
    isEditorLoaded = YES;
    viewPos.x = viewPos.y = 0;
    
    self.view = view;
    [view release];
}

- (void)viewDidUnload
{    
    [super viewDidUnload];

    if (isEditorLoaded) {
        destroy_editor();
        isEditorLoaded = NO;
    }

    self.panRecognizer = nil;

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

- (void)handlePan
{
    switch (panRecognizer.state) {
        case UIGestureRecognizerStateBegan:
            panStart = viewPos;
            break;
        case UIGestureRecognizerStateChanged:
        {
            CGPoint translation = [panRecognizer translationInView:self.view];
            viewPos.x = panStart.x - translation.x;
            viewPos.y = panStart.y - translation.y;
            editor_set_view_pos(viewPos);
            break;
        }
        case UIGestureRecognizerStateEnded:
        {
            // XXX fling
            break;
        }
        default:
            break;
    }
    editor_set_view_pos(viewPos);
}

- (NSInteger)preferredFramesPerSecond
{
    return 60;
}

- (void)glkView:(GLKView *)view drawInRect:(CGRect)rect
{
    render_editor();
}

@end
