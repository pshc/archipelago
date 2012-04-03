#import "ViewController.h"
#import "edit.h"

@interface ViewController () {
    BOOL isEditorLoaded;
}
@property (strong, nonatomic) EAGLContext *context;

@end

@implementation ViewController

@synthesize context = _context;

- (void)viewDidLoad
{
    [super viewDidLoad];
    
    self.context = [[[EAGLContext alloc] initWithAPI:kEAGLRenderingAPIOpenGLES2] autorelease];
    [EAGLContext setCurrentContext:self.context];

    CGRect frame = [[UIScreen mainScreen] applicationFrame];
    GLKView *view = [[GLKView alloc] initWithFrame:frame context:self.context];
    view.autoresizingMask = UIViewAutoresizingFlexibleHeight | UIViewAutoresizingFlexibleWidth;
    view.drawableDepthFormat = GLKViewDrawableDepthFormat24;

    create_editor();
    struct size size = {view.bounds.size.width, view.bounds.size.height};
    resize_editor(size);
    isEditorLoaded = YES;
    
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

#pragma mark - GLKView and GLKViewController delegate methods

/*
- (void)scrollWheel:(UIEvent *)theEvent
{
    CGFloat dx, dy;
    dx = theEvent.deltaX;
    dy = theEvent.deltaY;

    vec2 d = {-dx, -dy};
    editor_move_view_pos(d);
    self.needsDisplay = YES;
}
 */

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
