varying lowp vec2 uv;
uniform sampler2D atlas;

void main () {
    lowp vec4 col = texture2D(atlas, uv);
    gl_FragColor = vec4(uv, 1.0 - uv.x, col.a * (uv.y * 0.5 + 0.5));
}
