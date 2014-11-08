module Terrain.KernelSource

let kernelSource = @"
////////////////////////////////////////////////////////////////////////////////
 
__constant int P_MASK = 255;
__constant int P_SIZE = 256;
__constant int P[512] = {
 151, 160, 137,  91,  90,  15, 131,  13, 201,  95,  96,  53, 194, 233,   7, 225, 
 140,  36, 103,  30,  69, 142,   8,  99,  37, 240,  21,  10,  23, 190,   6, 148, 
 247, 120, 234,  75,   0,  26, 197,  62,  94, 252, 219, 203, 117,  35,  11,  32, 
  57, 177,  33,  88, 237, 149,  56,  87, 174,  20, 125, 136, 171, 168,  68, 175, 
  74, 165,  71, 134, 139,  48,  27, 166,  77, 146, 158, 231,  83, 111, 229, 122, 
  60, 211, 133, 230, 220, 105,  92,  41,  55,  46, 245,  40, 244, 102, 143,  54, 
  65,  25,  63, 161,   1, 216,  80,  73, 209,  76, 132, 187, 208,  89,  18, 169, 
 200, 196, 135, 130, 116, 188, 159,  86, 164, 100, 109, 198, 173, 186,   3,  64, 
  52, 217, 226, 250, 124, 123,   5, 202,  38, 147, 118, 126, 255,  82,  85, 212, 
 207, 206,  59, 227,  47,  16,  58,  17, 182, 189,  28,  42, 223, 183, 170, 213, 
 119, 248, 152,   2,  44, 154, 163,  70, 221, 153, 101, 155, 167,  43, 172,   9, 
 129,  22,  39, 253,  19,  98, 108, 110,  79, 113, 224, 232, 178, 185, 112, 104, 
 218, 246,  97, 228, 251,  34, 242, 193, 238, 210, 144,  12, 191, 179, 162, 241, 
  81,  51, 145, 235, 249,  14, 239, 107,  49, 192, 214,  31, 181, 199, 106, 157, 
 184,  84, 204, 176, 115, 121,  50,  45, 127,   4, 150, 254, 138, 236, 205,  93, 
 222, 114,  67,  29,  24,  72, 243, 141, 128, 195,  78,  66, 215,  61, 156, 180, 
 151, 160, 137,  91,  90,  15, 131,  13, 201,  95,  96,  53, 194, 233,   7, 225, 
 140,  36, 103,  30,  69, 142,   8,  99,  37, 240,  21,  10,  23, 190,   6, 148, 
 247, 120, 234,  75,   0,  26, 197,  62,  94, 252, 219, 203, 117,  35,  11,  32, 
  57, 177,  33,  88, 237, 149,  56,  87, 174,  20, 125, 136, 171, 168,  68, 175, 
  74, 165,  71, 134, 139,  48,  27, 166,  77, 146, 158, 231,  83, 111, 229, 122, 
  60, 211, 133, 230, 220, 105,  92,  41,  55,  46, 245,  40, 244, 102, 143,  54, 
  65,  25,  63, 161,   1, 216,  80,  73, 209,  76, 132, 187, 208,  89,  18, 169, 
 200, 196, 135, 130, 116, 188, 159,  86, 164, 100, 109, 198, 173, 186,   3,  64, 
  52, 217, 226, 250, 124, 123,   5, 202,  38, 147, 118, 126, 255,  82,  85, 212, 
 207, 206,  59, 227,  47,  16,  58,  17, 182, 189,  28,  42, 223, 183, 170, 213, 
 119, 248, 152,   2,  44, 154, 163,  70, 221, 153, 101, 155, 167,  43, 172,   9, 
 129,  22,  39, 253,  19,  98, 108, 110,  79, 113, 224, 232, 178, 185, 112, 104, 
 218, 246,  97, 228, 251,  34, 242, 193, 238, 210, 144,  12, 191, 179, 162, 241, 
  81,  51, 145, 235, 249,  14, 239, 107,  49, 192, 214,  31, 181, 199, 106, 157, 
 184,  84, 204, 176, 115, 121,  50,  45, 127,   4, 150, 254, 138, 236, 205,  93, 
 222, 114,  67,  29,  24,  72, 243, 141, 128, 195,  78,  66, 215,  61, 156, 180
};

////////////////////////////////////////////////////////////////////////////////
 
__constant int G_MASK = 15;
__constant int G_SIZE = 16;
__constant int G_VECSIZE = 4;
__constant int G[16*4] = {
     1.0f,  1.0f,  0.0f,  0.0f, 
    -1.0f,  1.0f,  0.0f,  0.0f, 
     1.0f, -1.0f,  0.0f,  0.0f, 
    -1.0f, -1.0f,  0.0f,  0.0f, 
     1.0f,  0.0f,  1.0f,  0.0f, 
    -1.0f,  0.0f,  1.0f,  0.0f, 
     1.0f,  0.0f, -1.0f,  0.0f, 
    -1.0f,  0.0f, -1.0f,  0.0f, 
     0.0f,  1.0f,  1.0f,  0.0f, 
     0.0f, -1.0f,  1.0f,  0.0f, 
     0.0f,  1.0f, -1.0f,  0.0f, 
     0.0f, -1.0f, -1.0f,  0.0f, 
     1.0f,  1.0f,  0.0f,  0.0f, 
    -1.0f,  1.0f,  0.0f,  0.0f, 
     0.0f, -1.0f,  1.0f,  0.0f, 
     0.0f, -1.0f, -1.0f,  0.0f   
 };

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
    return t*t*t*(t*(t*6.0f-15.0f)+10.0f); 
}
 
float4 normalized(float4 v)
{
    float d = sqrt(v.x * v.x + v.y * v.y + v.z * v.z);
    d = d > 0.0f ? d : 1.0f;
    float4 result = (float4)(v.x, v.y, v.z, 0.0f) / d;
    //result.w = 1.0f;
    return result;
}

float4 project(float4 v, float4 u)
{
    return dot(u, v) / dot(u, u) * u;
}

float4 orthonormalize(float4 v1, float4 v2)
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
 
float2 mix2d(float2 a, float2 b, float t)
{
    float2 ba = b - a;
    float2 tba = t * ba;
    float2 atba = a + tba;
    return atba;    
}
 
float4 mix3d(float4 a, float4 b, float t)
{
    float4 ba = b - a;
    float4 tba = t * ba;
    float4 atba = a + tba;
    return atba;    
}

//float4 mix4d(float4 a, float4 b, float t)
//{
//    float4 ba = b - a;
//    float4 tba = t * ba;
//    float4 atba = a + tba;
//    return atba;    
//}

////////////////////////////////////////////////////////////////////////////////
// Lattice points
////////////////////////////////////////////////////////////////////////////////
 
int lattice1d(int i)
{
    return P[i];
}
 
int lattice2d(int2 i)
{
    return P[i.x + P[i.y]];
}
 
int lattice3d(int4 i)
{
    return P[i.x + P[i.y + P[i.z]]];
}

//int lattice4d(int4 i)
//{
//    return P[i.x + P[i.y + P[i.z + P[i.w]]]];
//}

////////////////////////////////////////////////////////////////////////////////
// Gradients
////////////////////////////////////////////////////////////////////////////////

float gradient1d(int i, float v)
{
    int index = (lattice1d(i) & G_MASK) * G_VECSIZE;
    float g = G[index + 0];
    return (v * g);
}
 
float gradient2d(int2 i, float2 v)
{
    int index = (lattice2d(i) & G_MASK) * G_VECSIZE;
    float2 g = (float2)(G[index + 0], G[index + 1]);
    return dot(v, g);
}
 
float gradient3d(int4 i, float4 v)
{
    int index = (lattice3d(i) & G_MASK) * G_VECSIZE;
    float4 g = (float4)(G[index + 0], G[index + 1], G[index + 2], 1.0f);
    return dot(v, g);
}

//float gradient4d(int4 i, float4 v)
//{
//    int index = (lattice4d(i) & G_MASK) * G_VECSIZE;
//    float4 g = (float4)(G[index + 0], G[index + 1], G[index + 2], G[index + 3]);
//    return dot(v, g);
//}

////////////////////////////////////////////////////////////////////////////////
// Signed gradient noise
////////////////////////////////////////////////////////////////////////////////

float sgnoise1d(float position)
{
    float p = position;
    float pf = floor(p);
    int ip = (int)pf;
    float fp = p - pf;        
    ip &= P_MASK;
    
    float n0 = gradient1d(ip + 0, fp - 0.0f);
    float n1 = gradient1d(ip + 1, fp - 1.0f);
 
    float n = mix1d(n0, n1, smooth(fp));
    return n * (1.0f / 0.7f);
}
 
float sgnoise2d(float2 position)
{
    float2 p = position;
    float2 pf = floor(p);
    int2 ip = (int2)((int)pf.x, (int)pf.y);
    float2 fp = p - pf;        
    ip &= P_MASK;
    
    const int2 I00 = (int2)(0, 0);
    const int2 I01 = (int2)(0, 1);
    const int2 I10 = (int2)(1, 0);
    const int2 I11 = (int2)(1, 1);
    
    const float2 F00 = (float2)(0.0f, 0.0f);
    const float2 F01 = (float2)(0.0f, 1.0f);
    const float2 F10 = (float2)(1.0f, 0.0f);
    const float2 F11 = (float2)(1.0f, 1.0f);
 
    float n00 = gradient2d(ip + I00, fp - F00);
    float n10 = gradient2d(ip + I10, fp - F10);
    float n01 = gradient2d(ip + I01, fp - F01);
    float n11 = gradient2d(ip + I11, fp - F11);
 
    const float2 n0001 = (float2)(n00, n01);
    const float2 n1011 = (float2)(n10, n11);
 
    float2 n2 = mix2d(n0001, n1011, smooth(fp.x));
    float n = mix1d(n2.x, n2.y, smooth(fp.y));
    return n * (1.0f / 0.7f);
}
 
float sgnoise3d(float4 position)
{
 
    float4 p = position;
    float4 pf = floor(p);
    int4 ip = (int4)((int)pf.x, (int)pf.y, (int)pf.z, 0.0);
    float4 fp = p - pf;        
    ip &= P_MASK;
 
    int4 I000 = (int4)(0, 0, 0, 0);
    int4 I001 = (int4)(0, 0, 1, 0);  
    int4 I010 = (int4)(0, 1, 0, 0);
    int4 I011 = (int4)(0, 1, 1, 0);
    int4 I100 = (int4)(1, 0, 0, 0);
    int4 I101 = (int4)(1, 0, 1, 0);
    int4 I110 = (int4)(1, 1, 0, 0);
    int4 I111 = (int4)(1, 1, 1, 0);
    
    float4 F000 = (float4)(0.0f, 0.0f, 0.0f, 0.0f);
    float4 F001 = (float4)(0.0f, 0.0f, 1.0f, 0.0f);
    float4 F010 = (float4)(0.0f, 1.0f, 0.0f, 0.0f);
    float4 F011 = (float4)(0.0f, 1.0f, 1.0f, 0.0f);
    float4 F100 = (float4)(1.0f, 0.0f, 0.0f, 0.0f);
    float4 F101 = (float4)(1.0f, 0.0f, 1.0f, 0.0f);
    float4 F110 = (float4)(1.0f, 1.0f, 0.0f, 0.0f);
    float4 F111 = (float4)(1.0f, 1.0f, 1.0f, 0.0f);
    
    float n000 = gradient3d(ip + I000, fp - F000);
    float n001 = gradient3d(ip + I001, fp - F001);
    
    float n010 = gradient3d(ip + I010, fp - F010);
    float n011 = gradient3d(ip + I011, fp - F011);
    
    float n100 = gradient3d(ip + I100, fp - F100);
    float n101 = gradient3d(ip + I101, fp - F101);
 
    float n110 = gradient3d(ip + I110, fp - F110);
    float n111 = gradient3d(ip + I111, fp - F111);
 
    float4 n40 = (float4)(n000, n001, n010, n011);
    float4 n41 = (float4)(n100, n101, n110, n111);
 
    float4 n4 = mix3d(n40, n41, smooth(fp.x));
    float2 n2 = mix2d(n4.xy, n4.zw, smooth(fp.y));
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

float ugnoise2d(float2 position)
{
    return (0.5f - 0.5f * sgnoise2d(position));
}

float ugnoise3d(float4 position)
{
    return (0.5f - 0.5f * sgnoise3d(position));
}
 
////////////////////////////////////////////////////////////////////////////////

float turbulence3d(
    float4 position, 
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
    float4 pos = (float4)(x+s, y+s, z+s, 0.0f);
    
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

float4 TurbulenceShift(
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
    return (float4)(xd, yd, zd, 0.0f);
}

////////////////////////////////////////////////////////////////////////////////


__constant float FREQUENCY   = 0.05f;
__constant float LACUNARITY  =  1.5f;
__constant float PERSISTENCE = 0.68f;
__constant int   OCTAVES     =    24;
__constant int   SEED        =     1;

__kernel void VertexKernel( 
    __global float *vertices,
    __global float *normals,
    __global float *tangents,
    float4 BL, float4 BR, float4 TL,
    float rad, float amp)
{
    float eps = 0.0001f;

    int xIndex = get_global_id(0);
    int yIndex = get_global_id(1);
    
    int xSize = get_global_size(0);
    int ySize = get_global_size(1);
    
    float4 dX = (1.0f + eps) * (BR - BL);
    float4 dY = (1.0f + eps) * (TL - BL);
    
    float4 dx = 1.0f / ((float)xSize) * dX;
    float4 dy = 1.0f / ((float)ySize) * dY;
    
    float xP = ((float)xIndex) / ((float)xSize - 1.0f) - eps / 2.0f;
    float yP = ((float)yIndex) / ((float)ySize - 1.0f) - eps / 2.0f;
    
    float4 sc0 = normalize(BL + xP * dX + yP * dY);
    float4 sr0 = normalize(sc0 + dx);
    float4 sl0 = normalize(sc0 - dx);
    float4 st0 = normalize(sc0 + dy);
    float4 sb0 = normalize(sc0 - dy);
    
    float4 sc = rad * sc0;
    float4 sr = rad * sr0;
    float4 sl = rad * sl0;
    float4 st = rad * st0;
    float4 sb = rad * sb0;
    
    float vc = amp * Perlin(sc.x, sc.y, sc.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    float vr = amp * Perlin(sr.x, sr.y, sr.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    float vl = amp * Perlin(sl.x, sl.y, sl.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    float vt = amp * Perlin(st.x, st.y, st.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    float vb = amp * Perlin(sb.x, sb.y, sb.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    
    float4 tc = (rad + vc) * sc0;
    float4 tr = (rad + vr) * sr0;
    float4 tl = (rad + vl) * sl0;
    float4 tt = (rad + vt) * st0;
    float4 tb = (rad + vb) * sb0;
    
    float4 a = tr - tl;
    float4 b = tt - tb;
    
    float4 n = normalize(cross(a, b));
    float4 t = normalize(a);
    float4 t2 = normalize(b);
    
    int index = xIndex * ySize + yIndex;
    int index3 = 3 * index;
    int index4 = 4 * index;
    
    vertices[index3 + 0] = tc.x;
    vertices[index3 + 1] = tc.y;
    vertices[index3 + 2] = tc.z;
    
    normals[index3 + 0] = n.x;
    normals[index3 + 1] = n.y;
    normals[index3 + 2] = n.z;

    tangents[index4 + 0] = t.x;
    tangents[index4 + 1] = t.y;
    tangents[index4 + 2] = t.z;
    tangents[index4 + 3] = -1.0f;
}

//__kernel void VertexKernel( 
//    __global float *vertices,
//    __global float *normals,
//    __global float *tangents,
//    float4 BL, float4 BR, float4 TL,
//    float rad, float amp)
//{
//    float eps = 0.001f;
//
//    int xIndex = get_global_id(0);
//    int yIndex = get_global_id(1);
//    
//    int xSize = get_global_size(0);
//    int ySize = get_global_size(1);
//    
//    float4 dX = (BR - BL);
//    float4 dY = (TL - BL);
//    
//    float4 dx = 1.0f / ((float)xSize) * dX;
//    float4 dy = 1.0f / ((float)ySize) * dY;
//    
//    float xP = ((float)xIndex) / ((float)xSize - 1.0f);
//    float yP = ((float)yIndex) / ((float)ySize - 1.0f);
//    
//    float4 sc0 = normalize(BL + xP * dX + yP * dY);
//    float4 sr0 = normalize(sc0 + dx);
//    float4 sl0 = normalize(sc0 - dx);
//    float4 st0 = normalize(sc0 + dy);
//    float4 sb0 = normalize(sc0 - dy);
//    
//    float4 sc = rad * sc0;
//    float4 sr = rad * sr0;
//    float4 sl = rad * sl0;
//    float4 st = rad * st0;
//    float4 sb = rad * sb0;
//    
//    float vc = amp * Perlin(sc.x, sc.y, sc.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
//    float vr = amp * Perlin(sr.x, sr.y, sr.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
//    float vl = amp * Perlin(sl.x, sl.y, sl.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
//    float vt = amp * Perlin(st.x, st.y, st.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
//    float vb = amp * Perlin(sb.x, sb.y, sb.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
//    
//    float4 tc = (rad + vc) * sc0;
//    float4 tr = (rad + vr) * sr0;
//    float4 tl = (rad + vl) * sl0;
//    float4 tt = (rad + vt) * st0;
//    float4 tb = (rad + vb) * sb0;
//    
//    float4 a = tr - tl;
//    float4 b = tt - tb;
//    
//    float4 n = normalize(cross(a, b));
//    float4 t = normalize(a);
//    float4 t2 = normalize(b);
//    
//    int index = xIndex * ySize + yIndex;
//    int index3 = 3 * index;
//    int index4 = 4 * index;
//    
//    vertices[index3 + 0] = tc.x;
//    vertices[index3 + 1] = tc.y;
//    vertices[index3 + 2] = tc.z;
//    
//    normals[index3 + 0] = n.x;
//    normals[index3 + 1] = n.y;
//    normals[index3 + 2] = n.z;
//
//    tangents[index4 + 0] = t.x;
//    tangents[index4 + 1] = t.y;
//    tangents[index4 + 2] = t.z;
//    tangents[index4 + 3] = -1.0f;
//}

__constant float4 color[10] = 
{
    (float4)(0.000f, 0.000f, 0.000f, 0.000f),
    (float4)(0.249f, 0.091f, 0.338f, 0.000f),
    (float4)(0.511f, 0.177f, 0.428f, 0.000f),
    (float4)(0.788f, 0.260f, 0.271f, 0.000f),
    (float4)(0.916f, 0.388f, 0.124f, 0.000f),
    (float4)(0.986f, 0.529f, 0.077f, 0.000f),
    (float4)(1.000f, 0.683f, 0.130f, 0.000f),
    (float4)(1.000f, 0.816f, 0.371f, 0.000f),
    (float4)(1.000f, 0.921f, 0.661f, 0.000f),
    (float4)(1.000f, 1.000f, 1.000f, 0.000f)
};

__kernel void ColorizeKernel(
    __global uchar4 *heightMap,
    __global uchar4 *texture)
{
    int index = get_global_id(0);
    
    uchar4 pixel = heightMap[index];
    
    float value = (float)((int)(pixel.x)) / 255.0f;
    
    float p0 = value * 9.0f;
    int pos1 = (int)(floor(p0));
    int pos2 = min(pos1 + 1, 9);
    float p = fmod(p0, 1.0f);
    float4 color1 = color[pos1];
    float4 color2 = color[pos2];
    
    float4 newColor = (1.0f - p)*color1 + p*color2;
    
    uchar r = (int)(newColor.x * 255.0f);
    uchar g = (int)(newColor.y * 255.0f);
    uchar b = (int)(newColor.z * 255.0f);
    
    texture[index] = (uchar4)(r, g, b, 255);
}

__kernel void HeightMapKernel(
    __global uchar4 *output, 
    float4 BL, float4 BR, float4 TL, 
    float rad )
{
    int xIndex = get_global_id(0);
    int yIndex = get_global_id(1);
    
    float4 dX = (BR - BL);
    float4 dY = (TL - BL);
    
    int xSize = get_global_size(0);
    int ySize = get_global_size(1);
    
    float xP = ((float)xIndex - 1.0f) / ((float)xSize - 3.0f);
    float yP = ((float)yIndex - 1.0f) / ((float)ySize - 3.0f);
    
    //float len = length(dX);
    //float scale = 1.0f / len;
    float scale = 0.8f;
    
    float4 v = rad * normalized(BL + xP * dX + yP * dY);
    float value = scale * Perlin(v.x, v.y, v.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    
    int index = xIndex * ySize + yIndex;
    
    uchar c = (uchar)(clamp(255.0f * (value / 2.0f + 0.5f), 0.0f, 255.0f));
    
    output[index] = (uchar4)(c, c, c, 255);
}

__kernel void NormalMapKernel(
    __global uchar4 *heightMap, 
    __global uchar4 *normalMap)
{
    int xIndex = get_global_id(0);
    int yIndex = get_global_id(1);

    int xSize = get_global_size(0);
    int ySize = get_global_size(1);
    
    int x0 = clamp(xIndex - 1, 0, xSize);
    int x1 = xIndex;
    int x2 = clamp(xIndex + 1, 0, xSize);

    int y0 = clamp(yIndex - 1, 0, ySize) * xSize;
    int y1 = yIndex * xSize;
    int y2 = clamp(yIndex + 1, 0, ySize) * xSize;

    int i00 = (x0 + y0);
    int i10 = (x1 + y0);
    int i20 = (x2 + y0);
    int i01 = (x0 + y1);
    int i11 = (x1 + y1);
    int i21 = (x2 + y1);
    int i02 = (x0 + y2);
    int i12 = (x1 + y2);
    int i22 = (x2 + y2);
    
    float h00 = (float)heightMap[i00].x / 255.0f;
    float h10 = (float)heightMap[i10].x / 255.0f;
    float h20 = (float)heightMap[i20].x / 255.0f;

    float h01 = (float)heightMap[i01].x / 255.0f;
    float h11 = (float)heightMap[i11].x / 255.0f;
    float h21 = (float)heightMap[i21].x / 255.0f;

    float h02 = (float)heightMap[i02].x / 255.0f;
    float h12 = (float)heightMap[i12].x / 255.0f;
    float h22 = (float)heightMap[i22].x / 255.0f;
    
    float s = 2.0f;
    
    //tl = 00, t = 10, tr = 20
    // l = 01, c = 11,  r = 21
    //bl = 02, b = 12, br = 22
    
    float dX = (h20 + 2.0f * h21 + h22) - (h00 + 2.0f * h01 + h02);
    float dY = (h02 + 2.0f * h12 + h22) - (h00 + 2.0f * h10 + h20);
    float dZ = 1.0f / s;
    
    float4 n = normalize((float4)(dX, dY, dZ, 0.0f));

    uchar r = (int)clamp(255.0f * (n.x + 1.0f) / 2.0f, 0.0f, 255.0f);
    uchar g = (int)clamp(255.0f * (n.y + 1.0f) / 2.0f, 0.0f, 255.0f);
    //
    normalMap[i11] = (uchar4)(r, g, 255, 255);
}


__kernel void TextureKernel(
    __global uchar4 *heightMap,
    __global uchar4 *normalMap,
    float4 BL, float4 BR, float4 TL,
    float rad )
{
    int xIndex = get_global_id(0);
    int yIndex = get_global_id(1);

    int xSize = get_global_size(0);
    int ySize = get_global_size(1);

    float4 dX = (BR - BL);
    float4 dY = (TL - BL);
    
    float4 dx = 1.0f / ((float)xSize) * dX;
    float4 dy = 1.0f / ((float)ySize) * dY;

    float xP = ((float)xIndex - 1.0f) / ((float)xSize - 3.0f);
    float yP = ((float)yIndex - 1.0f) / ((float)ySize - 3.0f);

    float scale = 2.0f - 0.5f * length(dX);

    float4 v = rad * normalized(BL + xP * dX + yP * dY);
    float value = scale * Perlin(v.x, v.y, v.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);

    int index = xIndex * ySize + yIndex;
    
    uchar c = (uchar)(clamp(255.0f * (value / 2.0f + 0.5f), 0.0f, 255.0f));
    
    heightMap[index] = (uchar4)(c, c, c, 255);

    barrier(CLK_GLOBAL_MEM_FENCE);

    int x0 = clamp(xIndex - 1, 0, xSize);
    int x1 = xIndex;
    int x2 = clamp(xIndex + 1, 0, xSize);

    int y0 = clamp(yIndex - 1, 0, ySize) * xSize;
    int y1 = yIndex * xSize;
    int y2 = clamp(yIndex + 1, 0, ySize) * xSize;

    int i00 = (x0 + y0);
    int i10 = (x1 + y0);
    int i20 = (x2 + y0);
    int i01 = (x0 + y1);
    int i11 = (x1 + y1);
    int i21 = (x2 + y1);
    int i02 = (x0 + y2);
    int i12 = (x1 + y2);
    int i22 = (x2 + y2);
    
    float h00 = (float)heightMap[i00].x / 255.0f;
    float h10 = (float)heightMap[i10].x / 255.0f;
    float h20 = (float)heightMap[i20].x / 255.0f;

    float h01 = (float)heightMap[i01].x / 255.0f;
    float h11 = (float)heightMap[i11].x / 255.0f;
    float h21 = (float)heightMap[i21].x / 255.0f;

    float h02 = (float)heightMap[i02].x / 255.0f;
    float h12 = (float)heightMap[i12].x / 255.0f;
    float h22 = (float)heightMap[i22].x / 255.0f;
    
    float s = 2.0f;
    
    //tl = 00, t = 10, tr = 20
    // l = 01, c = 11,  r = 21
    //bl = 02, b = 12, br = 22
    
    float dXn = (h20 + 2.0f * h21 + h22) - (h00 + 2.0f * h01 + h02);
    float dYn = (h02 + 2.0f * h12 + h22) - (h00 + 2.0f * h10 + h20);
    float dZn = 1.0f / s;
    
    float4 n = normalize((float4)(dXn, dYn, dZn, 0.0f));
    uchar r = (int)clamp(255.0f * (n.x + 1.0f) / 2.0f, 0.0f, 255.0f);
    uchar g = (int)clamp(255.0f * (n.y + 1.0f) / 2.0f, 0.0f, 255.0f);

    normalMap[index] = (uchar4)(r, g, 255, 255);
}

__kernel void VertexValuesSplit( 
    __global float4 *output, 
    float4 BL, float4 BR, float4 TL,
    float rad, float amp)
{
    int gridIndex = get_global_id(0);
    int xIndex    = get_global_id(1);
    int yIndex    = get_global_id(2);
    
    int HIndex = gridIndex % 2;
    int VIndex = gridIndex / 2;
    
    float HShift = (float)HIndex;
    float VShift = (float)VIndex;
    
    float4 dX = (BR - BL)/2.0f;
    float4 dY = (TL - BL)/2.0f;
    
    int xSize = get_global_size(1);
    int ySize = get_global_size(2);
    
    float xP = ((float)xIndex) / ((float)xSize - 1.0f);
    float yP = ((float)yIndex) / ((float)ySize - 1.0f);
    
    float4 BLs = BL + HShift * dX + VShift * dY;
    
    float4 v0 = normalize(BLs + xP * dX + yP * dY);
    float4 v = rad * v0;
    
    float value = amp * Perlin(v.x, v.y, v.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    v = (rad + value) * v0;
    
    int index = gridIndex * xSize * ySize + xIndex * ySize + yIndex;
    
    output[index] = v;
}

__kernel void VertexNormalsSplit(
    __global float4 * output,
    float4 BL, float4 BR, float4 TL,
    float rad, float amp)
{
    int gridIndex = get_global_id(0);
    int xIndex    = get_global_id(1);
    int yIndex    = get_global_id(2);
    
    int HIndex = gridIndex % 2;
    int VIndex = gridIndex / 2;
    
    float HShift = (float)HIndex;
    float VShift = (float)VIndex;
    
    float4 dX = (BR - BL)/2.0f;
    float4 dY = (TL - BL)/2.0f;
    
    int xSize = get_global_size(1);
    int ySize = get_global_size(2);
    
    float xP = ((float)xIndex) / ((float)xSize - 1.0f);
    float yP = ((float)yIndex) / ((float)ySize - 1.0f);
    
    float4 BLs = BL + HShift * dX + VShift * dY;
    
    float4 dx = 1.0f / ((float)xSize) * dX;
    float4 dy = 1.0f / ((float)ySize) * dY;
    
    float4 sc0 = normalize(BLs + xP * dX + yP * dY);
    float4 sr0 = normalize(sc0 + dx);
    float4 sl0 = normalize(sc0 - dx);
    float4 st0 = normalize(sc0 + dy);
    float4 sb0 = normalize(sc0 - dy);
    
    float4 sr = rad * sr0;
    float4 sl = rad * sl0;
    float4 st = rad * st0;
    float4 sb = rad * sb0;
    
    float vr = amp * Perlin(sr.x, sr.y, sr.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    float vl = amp * Perlin(sl.x, sl.y, sl.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    float vt = amp * Perlin(st.x, st.y, st.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    float vb = amp * Perlin(sb.x, sb.y, sb.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    
    float4 tr = (rad + vr) * sr;
    float4 tl = (rad + vl) * sl;
    float4 tt = (rad + vt) * st;
    float4 tb = (rad + vb) * sb;
    
    float4 a = tr - tl;
    float4 b = tt - tb;
    
    float4 n = normalize(cross(a, b));
    
    int index = gridIndex * xSize * ySize + xIndex * ySize + yIndex;
    
    output[index] = n;
}


__kernel void HeightMapSplit( 
    __global uchar *output, 
    float4 BL, float4 BR, float4 TL, 
    float rad )
{
    
    int gridIndex = get_global_id(0);
    int xIndex    = get_global_id(1);
    int yIndex    = get_global_id(2);
    
    int HIndex = gridIndex % 2;
    int VIndex = gridIndex / 2;
    
    float HShift = (float)HIndex;
    float VShift = (float)VIndex;
    
    float4 dX = (BR - BL)/2.0f;
    float4 dY = (TL - BL)/2.0f;
    
    int xSize = get_global_size(1);
    int ySize = get_global_size(2);

    float xP = ((float)xIndex - 1.0f) / ((float)xSize - 3.0f);
    float yP = ((float)yIndex - 1.0f) / ((float)ySize - 3.0f);
    
    float4 BLs = BL + HShift * dX + VShift * dY;
    
    float scale = 1.0f - 0.5f * length(dX);
    
    float4 v = rad * normalized(BLs + xP * dX + yP * dY);
    float value = scale * Perlin(v.x, v.y, v.z, FREQUENCY, LACUNARITY, PERSISTENCE, OCTAVES, SEED);
    
    int index = gridIndex * xSize * ySize + xIndex * ySize + yIndex;
    
    output[index] = (uchar)(clamp(255.0f * (value / 2.0f + 0.5f), 0.0f, 255.0f));
}

__kernel void NormalMapSplit(
    __global uchar  *heightMaps, 
    __global uchar2 *normalMaps )
{
    int gridIndex = get_global_id(0);
    int xIndex    = get_global_id(1);
    int yIndex    = get_global_id(2);

    int xSize = get_global_size(1);
    int ySize = get_global_size(2);
    
    int o = gridIndex * xSize * ySize;
    
    int x0 = clamp(xIndex - 1, 0, xSize);
    int x1 = xIndex;
    int x2 = clamp(xIndex + 1, 0, xSize);

    int y0 = clamp(yIndex - 1, 0, ySize) * xSize;
    int y1 = yIndex * xSize;
    int y2 = clamp(yIndex + 1, 0, ySize) * xSize;

    int i00 = o + x0 + y0;
    int i10 = o + x1 + y0;
    int i20 = o + x2 + y0;
    int i01 = o + x0 + y1;
    int i11 = o + x1 + y1;
    int i21 = o + x2 + y1;
    int i02 = o + x0 + y2;
    int i12 = o + x1 + y2;
    int i22 = o + x2 + y2;
    
    float h00 = (float)heightMaps[i00] / 255.0f;
    float h10 = (float)heightMaps[i10] / 255.0f;
    float h20 = (float)heightMaps[i20] / 255.0f;

    float h01 = (float)heightMaps[i01] / 255.0f;
    float h11 = (float)heightMaps[i11] / 255.0f;
    float h21 = (float)heightMaps[i21] / 255.0f;

    float h02 = (float)heightMaps[i02] / 255.0f;
    float h12 = (float)heightMaps[i12] / 255.0f;
    float h22 = (float)heightMaps[i22] / 255.0f;
    
    float s = 2.0f;
    
    //tl = 00, t = 10, tr = 20
    // l = 01, c = 11,  r = 21
    //bl = 02, b = 12, br = 22
    
    float dX = (h20 + 2.0f * h21 + h22) - (h00 + 2.0f * h01 + h02);
    float dY = (h02 + 2.0f * h12 + h22) - (h00 + 2.0f * h10 + h20);
    float dZ = 1.0f / s;
    
    float4 n = normalize((float4)(dX, dY, dZ, 0.0f));

    uchar r = (uchar)clamp(255.0f * (n.x + 1.0f) / 2.0f, 0.0f, 255.0f);
    uchar g = (uchar)clamp(255.0f * (n.y + 1.0f) / 2.0f, 0.0f, 255.0f);
    //
    normalMaps[i11] = (uchar2)(r, g);
}

"