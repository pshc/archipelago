#ifndef PLATFORM_H
#define PLATFORM_H

#if defined (__IPHONE_OS_VERSION_MIN_REQUIRED)
# include <OpenGLES/ES2/gl.h>
#else
# include <OpenGL/gl.h>
#endif

void setup_platform(void);
void cleanup_platform(void);

char *read_shader(const char *name, const char *ext);
char *module_path(const char *cat, const char *hash);


#endif /* PLATFORM_H */