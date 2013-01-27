#import "EditorViewController.h"
#import "FlickDynamics.h"
#import "Editor_visual.h"

@interface EditorViewController () {
    void *VISUAL_ENV;
}
@property (strong, nonatomic) EAGLContext *context;
@property (strong, nonatomic) FlickDynamics *flickDynamics;
@end

@implementation EditorViewController

- (void)loadView
{
    self.view = [[GLKView alloc] initWithFrame:[[UIScreen mainScreen] applicationFrame]];
}

- (void)viewDidLoad
{
    [super viewDidLoad];
    
    self.preferredFramesPerSecond = 60;
    
    self.context = [[EAGLContext alloc] initWithAPI:kEAGLRenderingAPIOpenGLES2];

    if (!self.context) {
        NSLog(@"Failed to create ES context");
        return;
    }

    GLKView *view = (GLKView *) self.view;
    view.context = self.context;
    view.drawableDepthFormat = GLKViewDrawableDepthFormat24;

    [EAGLContext setCurrentContext:self.context];

    VISUAL_ENV = setup_editor();
    if (!load_shader(VISUAL_ENV))
        NSAssert(NO, @"Exiting due to missing shader.");
    set_view_pos(0, 0, VISUAL_ENV);
    set_view_size(view.bounds.size.width, view.bounds.size.height, VISUAL_ENV);

    self.flickDynamics = [FlickDynamics flickDynamicsWithViewportWidth:1 viewportHeight:1 scrollBoundsLeft:-1 scrollBoundsTop:-1 scrollBoundsRight:10 scrollBoundsBottom:10];

    NSLog(@"Preparations complete.");
}

- (void)dealloc
{    
    if (VISUAL_ENV) {
        [EAGLContext setCurrentContext:self.context];
        cleanup_editor(VISUAL_ENV);
    }
    
    if ([EAGLContext currentContext] == self.context) {
        [EAGLContext setCurrentContext:nil];
    }
}

- (void)didReceiveMemoryWarning
{
    [super didReceiveMemoryWarning];

    if ([self isViewLoaded] && ([[self view] window] == nil)) {
        self.view = nil;

        if (VISUAL_ENV) {
            [EAGLContext setCurrentContext:self.context];
            cleanup_editor(VISUAL_ENV);
            VISUAL_ENV = NULL;
        }

        if ([EAGLContext currentContext] == self.context) {
            [EAGLContext setCurrentContext:nil];
        }
        self.context = nil;
    }
}

- (void)touchesBegan:(NSSet *)touches withEvent:(UIEvent *)event
{
    UITouch *touch = [touches anyObject];
    CGPoint where = [touch locationInView:self.view];
    [self.flickDynamics startTouchAtX:where.x / 320 y:where.y / 460];
}

- (void)touchesMoved:(NSSet *)touches withEvent:(UIEvent *)event
{
    UITouch *touch = [touches anyObject];
    CGPoint where = [touch locationInView:self.view];
    [self.flickDynamics moveTouchAtX:where.x / 320 y:where.y / 460];
}

- (void)touchesEnded:(NSSet *)touches withEvent:(UIEvent *)event
{
    UITouch *touch = [touches anyObject];
    CGPoint where = [touch locationInView:self.view];
    [self.flickDynamics endTouchAtX:where.x / 320 y:where.y / 460];
}

- (void)update
{
    [self.flickDynamics animate];
    set_view_pos(self.flickDynamics.currentScrollLeft*320, self.flickDynamics.currentScrollTop*460, VISUAL_ENV);
}

- (void)glkView:(GLKView *)view drawInRect:(CGRect)rect
{
    render_editor(VISUAL_ENV);
}

@end
