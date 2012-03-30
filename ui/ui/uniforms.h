#ifndef UNIFORMS_H
#define UNIFORMS_H

#ifndef UNIFORM
# define UNIFORM_SPEC(spec) extern struct spec spec; extern const char * const _spec_##spec[]; struct spec
# define UNIFORM(name) unsigned int name;
#endif

UNIFORM_SPEC(uniform) {
    UNIFORM(projectionMatrix)
    UNIFORM(modelViewMatrix)
    UNIFORM(atlas)
    UNIFORM(invAtlasSize)
};

#undef UNIFORM_SPEC
#undef UNIFORM

#endif
