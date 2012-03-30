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