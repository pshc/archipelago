attribute lowp vec2 position;
attribute lowp vec2 texCoord0;

varying lowp vec2 uv;

uniform mat4 modelViewMatrix;
uniform mat4 projectionMatrix;
uniform lowp vec2 invAtlasSize;

void main() {
    uv = texCoord0 * invAtlasSize;
    gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 0.0, 1.0);
}