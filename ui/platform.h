#ifndef PLATFORM_H
#define PLATFORM_H

#if defined (__IPHONE_OS_VERSION_MIN_REQUIRED)
# include <OpenGLES/ES2/gl.h>
#else
# include <OpenGL/gl.h>
#endif

char *read_resource(const char *name);

#endif /* PLATFORM_H */