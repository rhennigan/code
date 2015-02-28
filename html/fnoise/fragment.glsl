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
uniform float G[16*4];
uniform int order;
uniform float p;
uniform float aspect;

varying vec2 pos;

////////////////////////////////////////////////////////////////////////////////

const int P_MASK = 255;
const int P_SIZE = 256;

////////////////////////////////////////////////////////////////////////////////

const int G_MASK    = 15;
const int G_SIZE    = 16;
const int G_VECSIZE =  4;

////////////////////////////////////////////////////////////////////////////////

//int mod(int x, int a)
//{
//    int n = (x / a);
//    int v = v - n * a;
//    if ( v < 0 )
//        v += a;
//    return v;   
//}
 
float smooth(float t)
{
    return t*t*t*(t*(t*6.0-15.0)+10.0); 
}
 
vec4 normalized(vec4 v)
{
    float d = sqrt(v.x * v.x + v.y * v.y + v.z * v.z);
    d = d > 0.0 ? d : 1.0;
    vec4 result = vec4(v.x, v.y, v.z, 0.0) / d;
    //result.w = 1.0f;
    return result;
}

vec4 project(vec4 v, vec4 u)
{
    return dot(u, v) / dot(u, u) * u;
}

vec4 orthonormalize(vec4 v1, vec4 v2)
{
    return normalize(v2 - project(v2, v1));
}

////////////////////////////////////////////////////////////////////////////////

float mix1d(float a, float b, float t)
{
    float ba = b - a;
    float tba = t * ba;
    float atba = a + tba;
    return atba;    
}
 
vec2 mix2d(vec2 a, vec2 b, float t)
{
    vec2 ba = b - a;
    vec2 tba = t * ba;
    vec2 atba = a + tba;
    return atba;    
}
 
vec4 mix3d(vec4 a, vec4 b, float t)
{
    vec4 ba = b - a;
    vec4 tba = t * ba;
    vec4 atba = a + tba;
    return atba;    
}

//vec4 mix4d(vec4 a, vec4 b, float t)
//{
//    vec4 ba = b - a;
//    vec4 tba = t * ba;
//    vec4 atba = a + tba;
//    return atba;    
//}

////////////////////////////////////////////////////////////////////////////////
// Lattice points
////////////////////////////////////////////////////////////////////////////////
 
int lattice1d(int i)
{
    return P[i];
}
 
int lattice2d(ivec2 i)
{
    return P[i.x + P[i.y]];
}
 
int lattice3d(ivec4 i)
{
    return P[i.x + P[i.y + P[i.z]]];
}

//int lattice4d(ivec4 i)
//{
//    return P[i.x + P[i.y + P[i.z + P[i.w]]]];
//}

////////////////////////////////////////////////////////////////////////////////
// Gradients
////////////////////////////////////////////////////////////////////////////////

float gradient1d(int i, float v)
{
    int index = int(mod(float(lattice1d(i)), float(G_SIZE))) * G_VECSIZE;
    float g = G[index + 0];
    return (v * g);
}

float gradient2d(ivec2 i, vec2 v)
{
    int index = (lattice2d(i) & G_MASK) * G_VECSIZE;
    vec2 g = vec2(G[index + 0], G[index + 1]);
    return dot(v, g);
}
 
float gradient3d(ivec4 i, vec4 v)
{
    int index = (lattice3d(i) & G_MASK) * G_VECSIZE;
    vec4 g = vec4(G[index + 0], G[index + 1], G[index + 2], 1.0f);
    return dot(v, g);
}

//float gradient4d(ivec4 i, vec4 v)
//{
//    int index = (lattice4d(i) & G_MASK) * G_VECSIZE;
//    vec4 g = (vec4)(G[index + 0], G[index + 1], G[index + 2], G[index + 3]);
//    return dot(v, g);
//}

////////////////////////////////////////////////////////////////////////////////
// Signed gradient noise
////////////////////////////////////////////////////////////////////////////////

float sgnoise1d(float position)
{
    float p = position;
    float pf = floor(p);
    int ip = int(pf);
    float fp = p - pf;        
    ip &= P_MASK;
    
    float n0 = gradient1d(ip + 0, fp - 0.0f);
    float n1 = gradient1d(ip + 1, fp - 1.0f);
 
    float n = mix1d(n0, n1, smooth(fp));
    return n * (1.0f / 0.7f);
}
 
float sgnoise2d(vec2 position)
{
    vec2 p = position;
    vec2 pf = floor(p);
    ivec2 ip = ivec2(int(pf.x), int(pf.y));
    vec2 fp = p - pf;        
    ip &= P_MASK;
    
    const ivec2 I00 = ivec2(0, 0);
    const ivec2 I01 = ivec2(0, 1);
    const ivec2 I10 = ivec2(1, 0);
    const ivec2 I11 = ivec2(1, 1);
    
    const vec2 F00 = vec2(0.0f, 0.0f);
    const vec2 F01 = vec2(0.0f, 1.0f);
    const vec2 F10 = vec2(1.0f, 0.0f);
    const vec2 F11 = vec2(1.0f, 1.0f);
 
    float n00 = gradient2d(ip + I00, fp - F00);
    float n10 = gradient2d(ip + I10, fp - F10);
    float n01 = gradient2d(ip + I01, fp - F01);
    float n11 = gradient2d(ip + I11, fp - F11);
 
    const vec2 n0001 = vec2(n00, n01);
    const vec2 n1011 = vec2(n10, n11);
 
    vec2 n2 = mix2d(n0001, n1011, smooth(fp.x));
    float n = mix1d(n2.x, n2.y, smooth(fp.y));
    return n * (1.0f / 0.7f);
}
 
float sgnoise3d(vec4 position)
{
 
    vec4 p = position;
    vec4 pf = floor(p);
    ivec4 ip = ivec4(int(pf.x), int(pf.y), int(pf.z), 0.0);
    vec4 fp = p - pf;        
    ip &= P_MASK;
 
    ivec4 I000 = ivec4(0, 0, 0, 0);
    ivec4 I001 = ivec4(0, 0, 1, 0);  
    ivec4 I010 = ivec4(0, 1, 0, 0);
    ivec4 I011 = ivec4(0, 1, 1, 0);
    ivec4 I100 = ivec4(1, 0, 0, 0);
    ivec4 I101 = ivec4(1, 0, 1, 0);
    ivec4 I110 = ivec4(1, 1, 0, 0);
    ivec4 I111 = ivec4(1, 1, 1, 0);
    
    vec4 F000 = vec4(0.0f, 0.0f, 0.0f, 0.0f);
    vec4 F001 = vec4(0.0f, 0.0f, 1.0f, 0.0f);
    vec4 F010 = vec4(0.0f, 1.0f, 0.0f, 0.0f);
    vec4 F011 = vec4(0.0f, 1.0f, 1.0f, 0.0f);
    vec4 F100 = vec4(1.0f, 0.0f, 0.0f, 0.0f);
    vec4 F101 = vec4(1.0f, 0.0f, 1.0f, 0.0f);
    vec4 F110 = vec4(1.0f, 1.0f, 0.0f, 0.0f);
    vec4 F111 = vec4(1.0f, 1.0f, 1.0f, 0.0f);
    
    float n000 = gradient3d(ip + I000, fp - F000);
    float n001 = gradient3d(ip + I001, fp - F001);
    
    float n010 = gradient3d(ip + I010, fp - F010);
    float n011 = gradient3d(ip + I011, fp - F011);
    
    float n100 = gradient3d(ip + I100, fp - F100);
    float n101 = gradient3d(ip + I101, fp - F101);
 
    float n110 = gradient3d(ip + I110, fp - F110);
    float n111 = gradient3d(ip + I111, fp - F111);
 
    vec4 n40 = vec4(n000, n001, n010, n011);
    vec4 n41 = vec4(n100, n101, n110, n111);
 
    vec4 n4 = mix3d(n40, n41, smooth(fp.x));
    vec2 n2 = mix2d(n4.xy, n4.zw, smooth(fp.y));
    float n = mix1d(n2.x, n2.y, smooth(fp.z));
    return n * (1.0f / 0.7f);
}


////////////////////////////////////////////////////////////////////////////////
// Unsigned gradient noise
////////////////////////////////////////////////////////////////////////////////
 
float ugnoise1d(float position)
{
    return (0.5f - 0.5f * sgnoise1d(position));
}

float ugnoise2d(vec2 position)
{
    return (0.5f - 0.5f * sgnoise2d(position));
}

float ugnoise3d(vec4 position)
{
    return (0.5f - 0.5f * sgnoise3d(position));
}
 
////////////////////////////////////////////////////////////////////////////////

float turbulence3d(
    vec4 position, 
    float frequency,
    float lacunarity, 
    float increment, 
    float octaves)
{
    int i = 0;
    float fi = 0.0f;
    float remainder = 0.0f; 
    float sample = 0.0f;    
    float value = 0.0f;
    int iterations = (int)octaves;
    
    for (i = 0; i < iterations; i++)
    {
        fi = (float)i;
        sample = (1.0f - 2.0f * sgnoise3d(position * frequency));
        sample *= pow( lacunarity, -fi * increment );
        value += fabs(sample);
        frequency *= lacunarity;
    }
    
    remainder = octaves - (float)iterations;
    if ( remainder > 0.0f )
    {
        sample = remainder * (1.0f - 2.0f * sgnoise3d(position * frequency));
        sample *= pow( lacunarity, -fi * increment );
        value += fabs(sample);
    }
        
    return value;   
}

////////////////////////////////////////////////////////////////////////////////

float MakeInt32Range(float value)
{
    if (value >= 1073741824.0f) 
    {
        return (2.0f * remainder(value, 1073741824.0f)) - 1073741824.0f; 
    }
    else if (value <= -1073741824.0f) 
    {
        return (2.0f * remainder(value, 1073741824.0f)) + 1073741824.0f;
    }
    else
    {
        return value;
    }
    
}

float GradientCoherentNoise3D(float x, float y, float z, int seed)
{
    float s = (float)seed;
    vec4 pos = (vec4)(x+s, y+s, z+s, 0.0f);
    
    return sgnoise3d(pos);
}

float Perlin(float x, float y, float z, 
    float frequency, float lacunarity, float persistence,
    int octaves, int seed)
{
    seed = seed + 0;
    
    float value = 0.0f;
    float signal = 0.0f;
    float cp = 1.0f;
    
    x *= frequency;
    y *= frequency;
    z *= frequency;
    for (int i = 0; i < octaves; i++)
    {
        float nx = MakeInt32Range(x);
        float ny = MakeInt32Range(y);
        float nz = MakeInt32Range(z);
        seed = (seed + i) & 0xffffffff;
        signal = GradientCoherentNoise3D(nx, ny, nz, seed);
        value += signal * cp;
        x *= lacunarity;
        y *= lacunarity;
        z *= lacunarity;
        cp *= persistence;
    }
    return value;
}

float RidgedMultifractal(float x, float y, float z, 
    float frequency, float lacunarity, int octaves, 
    int seed)
{
    
    x *= frequency;
    y *= frequency;
    z *= frequency;
    
    float signal = 0.0f;
    float value = 0.0f;
    float weight = 1.0f;
    float offset = 1.0f;
    float gain = 2.0f;
    float f = 1.0f;
    
    for(int i = 0; i < octaves; i++)
    {
        float nx = MakeInt32Range(x);
        float ny = MakeInt32Range(y);
        float nz = MakeInt32Range(z);
        seed = (seed + i) & 0x7fffffff;
        signal = GradientCoherentNoise3D(nx, ny, nz, seed);
        signal = fabs(signal);
        signal = offset - signal;
        signal *= signal;
        signal *= weight;
        weight = signal * gain;
        if (weight > 1.0f) { weight = 1.0f; }
        if (weight < 0.0f) { weight = 0.0f; }
        value += (signal * pow(f, -1.0f));
        f *= lacunarity;
        x *= lacunarity;
        y *= lacunarity;
        z *= lacunarity;
    }
    
    return (value * 1.25f) - 1.0f;
}

float Billow(float x, float y, float z, 
    float frequency, float lacunarity, float persistence,
    int octaves, int seed)
{
    float value = 0.0f;
    float signal = 0.0f;
    float curp = 1.0f;
    float nx, ny, nz;
    x *= frequency;
    y *= frequency;
    z *= frequency;
    for(int i = 0; i < octaves; i++)
    {
        nx = MakeInt32Range(x);
        ny = MakeInt32Range(y);
        nz = MakeInt32Range(z);
        seed = (seed + i) & 0x7fffffff;
        signal = GradientCoherentNoise3D(nx, ny, nz, seed);
        signal = 2.0f * fabs(signal) - 1.0f;
        value += signal * curp;
        x *= lacunarity;
        y *= lacunarity;
        z *= lacunarity;
        curp *= persistence;
    }

    return value + 0.5f;
}

float ScaleBias(float value, float scale, float bias)
{
    return value * scale + bias;
}

float MapCubicSCurve(float value)
{
    return (value * value * (3.0f - 2.0f * value));
}

float InterpolateLinear(float a, float b, float position)
{
    return ((1.0f - position) * a) + (position * b);
}

float Select(float value1, float value2, float selector, 
    float selectMin, float selectMax, float fallOff)
{
    float cv = selector;
    if (fallOff > 0.0f)
    {
        if (cv < (selectMin - fallOff)) { return value1; }
        else if (cv < (selectMin + fallOff))
        {
            float lc = (selectMin - fallOff);
            float uc = (selectMin + fallOff);
            float a = MapCubicSCurve((cv - lc) / (uc - lc));
            return InterpolateLinear(value1, value2, a);

        }
        else if (cv < (selectMax - fallOff)) { return value2; }
        else if (cv < (selectMax + fallOff))
        {
            float lc = (selectMax - fallOff);
            float uc = (selectMax + fallOff);
            float a = MapCubicSCurve((cv - lc) / (uc - lc));
            return InterpolateLinear(value2, value1, a);

        }
        return value1;
    }
    else
    {
        if (cv < selectMin || cv > selectMax) { return value1; }
        return value2;
    }
}

vec4 TurbulenceShift(
    float x, float y, float z,
    float power, float frequency, 
    int octaves, int seed)
{
    float X0 = (12414.0f / 65536.0f);
    float Y0 = (65124.0f / 65536.0f);
    float Z0 = (31337.0f / 65536.0f);
    float X1 = (26519.0f / 65536.0f);
    float Y1 = (18128.0f / 65536.0f);
    float Z1 = (60493.0f / 65536.0f);
    float X2 = (53820.0f / 65536.0f);
    float Y2 = (11213.0f / 65536.0f);
    float Z2 = (44845.0f / 65536.0f);
    
    float xD = Perlin(x+X0, y+Y0, z+Z0, frequency, 2.0f, 0.5f, octaves, seed+0);
    float yD = Perlin(x+X1, y+Y1, z+Z1, frequency, 2.0f, 0.5f, octaves, seed+1);
    float zD = Perlin(x+X2, y+Y2, z+Z2, frequency, 2.0f, 0.5f, octaves, seed+2);
    
    float xd = x + power * xD;
    float yd = y + power * yD;
    float zd = z + power * zD;
    return (vec4)(xd, yd, zd, 0.0f);
}

////////////////////////////////////////////////////////////////////////////////



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