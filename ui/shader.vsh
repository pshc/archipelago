attribute vec2 position;
attribute vec2 texCoord0;

varying vec2 uv;

uniform mat4 modelViewMatrix;
uniform mat4 projectionMatrix;
uniform vec2 invAtlasSize;

void main() {
    uv = texCoord0 * invAtlasSize;
    gl_Position = projectionMatrix * modelViewMatrix * vec4(position, 0.0, 1.0);
}