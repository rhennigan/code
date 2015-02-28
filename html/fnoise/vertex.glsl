attribute vec3 position;
attribute vec2 texCoord1;

uniform mat4 worldMatrix;
uniform mat4 projectionMatrix;

varying vec2 pos;
void main(void) {
  gl_Position = projectionMatrix * worldMatrix * vec4(position, 1.0);
  pos = texCoord1;
}