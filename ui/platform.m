#import "platform.h"

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

#if defined (__IPHONE_OS_VERSION_MIN_REQUIRED)
static NSBundle *bundle = nil;

void setup_platform(void) {
    bundle = [[NSBundle alloc] initWithPath:[[NSBundle mainBundle] pathForResource:@"forms" ofType:@"bundle"]];
}

void cleanup_platform(void) {
    [bundle release];
    bundle = nil;
}

char *module_path(const char *cat, const char *name) {
    NSString *resourceName = [NSString stringWithCString:name encoding:NSUTF8StringEncoding];
    NSString *subdir = [NSString stringWithCString:cat encoding:NSUTF8StringEncoding];
    NSString *path = [bundle pathForResource:resourceName ofType:@"" inDirectory:subdir];
    if (!path) {
        return NULL;
    }
    return strdup([path cStringUsingEncoding:NSUTF8StringEncoding]);
}
#else
static char *base_dir = NULL;

void setup_platform(void) {
    base_dir = strdup(__FILE__);
    *(strrchr(base_dir, '/') + 1) = '\0';
}

void cleanup_platform(void) {
    free(base_dir);
    base_dir = NULL;
}

char *module_path(const char *cat, const char *name) {
    char *full = malloc(strlen(base_dir) + strlen(cat) + strlen(name) + 5);
    sprintf(full, "%s../%s/%s", base_dir, cat, name);
    return full;
}
#endif
