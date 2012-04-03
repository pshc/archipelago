varying lowp vec2 uv;
uniform sampler2D atlas;

void main () {
    lowp vec4 col = texture2D(atlas, uv);
    gl_FragColor = vec4(col.rg * uv, col.b * (1.0 - uv.x), col.a * (uv.y * 0.5 + 0.5));
}
