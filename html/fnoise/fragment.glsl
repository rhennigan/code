////////////////////////////////////////////////////////////////////////////////

const int P_MASK = 255;
const int P_SIZE = 256;

////////////////////////////////////////////////////////////////////////////////

const int G_MASK = 15;
const int G_SIZE = 16;
const int G_VECSIZE = 4;

////////////////////////////////////////////////////////////////////////////////
 

#ifdef GL_ES
precision highp float;
#endif

#define S(x, a, b) ((x) < (a) ? (a) : (x) > (b) ? (b) : (x))
#define INT(x, a, b) (((x) - (a)) / ((b) - (a)))

#define PI 3.1415926535
#define SCALE 65.0
#define MAG 5.0

#define c11 0.843
#define c12 0.878
#define c13 0.898

#define cr1 0.839
#define cr2 0.290
#define cr3 0.152

#define c21 0.047
#define c22 0.352
#define c23 0.505

#define c31 0.000
#define c32 0.000
#define c33 0.000

#define c41 0.556
#define c42 0.678
#define c43 0.670

#define c51 1.000
#define c52 1.000
#define c53 1.000

uniform sampler2D sampler1;
uniform int P[512];
uniform int order;
uniform float p;
uniform float aspect;

varying vec2 pos;

vec4 color_px(float val, float p) {
  const float p1 = 0.00;
  const float p2 = 0.50;
  const float p3 = 0.90;

  float t = 0.5 * (sin(4.0 * p) + 1.0);

  vec4 col = vec4(0.0, 0.0, 0.0, 1.0);
  float v = S(val, 0.0, 1.0);
  if (v <= -0.00001) {
    col[0] = 0.0;
    col[1] = 0.0;
    col[2] = 0.0;
  } else if (v < p1) {
    float t2 = INT(v, 0.0, p1);
    float t1 = 1.0 - t2;
    col[0] = t1 * c11 + t2 * (t*c21+(1.0-t)*cr1);
    col[1] = t1 * c12 + t2 * (t*c22+(1.0-t)*cr2);
    col[2] = t1 * c13 + t2 * (t*c23+(1.0-t)*cr3);
  } else if (v < p2) {
    float t2 = INT(v, p1, p2);
    float t1 = 1.0 - t2;
    col[0] = t1 * (t*c21+(1.0-t)*cr1) + t2 * c31;
    col[1] = t1 * (t*c22+(1.0-t)*cr2) + t2 * c32;
    col[2] = t1 * (t*c23+(1.0-t)*cr3) + t2 * c33;
  } else if (v < p3) {
    float t2 = INT(v, p2, p3);
    float t1 = 1.0 - t2;
    col[0] = t1 * c31 + t2 * c41;
    col[1] = t1 * c32 + t2 * c42;
    col[2] = t1 * c33 + t2 * c43;
  } else {
    float t2 = INT(v, p3, 1.0);
    float t1 = 1.0 - t2;
    col[0] = t1 * c41 + t2 * c51;
    col[1] = t1 * c42 + t2 * c52;
    col[2] = t1 * c43 + t2 * c53;
  }

  return col;
}

void main(void) {
  float d = float(order);
  float sum = 0.0;
  float dX = 0.5 * p;
  float dY = 0.4 * p;
  float s = SCALE * (sin(p) + 1.5) + float(5*order);

  // float x = pos.x + dX;
  // float y = pos.y + dY;

  float x = dX + aspect * pos.x * cos(p) - pos.y * sin(p);
  float y = dY + pos.y * cos(p) + aspect * pos.x * sin(p);

  for (int k = 0; k < 30; k++) {
    if (k < order) {
      sum += cos(s * x * cos(float(k) * PI / d) - 
                 s * y * sin(float(k) * PI / d) + 40.0*p);
    }
  }
  sum *= MAG;
  sum = atan(sum) / (1.0 * PI) + 0.5;

  // vec4 color = vec4(sum, sum, sum, 1.0);
  vec4 color = color_px(sum, p);

  gl_FragColor = color;
}