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

#define c21 0.047
#define c22 0.352
#define c23 0.505

#define c31 0.000
#define c32 0.000
#define c33 0.000

#define c41 0.839
#define c42 0.290
#define c43 0.152

#define c51 1.000
#define c52 1.000
#define c53 1.000

////////////////////////////////////////////////////////////////////////////////

uniform sampler2D sampler1;
uniform float p;
uniform float aspect;

varying vec2 pos;

////////////////////////////////////////////////////////////////////////////////
// UTILITIES
////////////////////////////////////////////////////////////////////////////////

#define WRAP 128.0
#define SHFL  34.0

vec3 wrap(vec3 v) {
  return v - WRAP * floor(v / WRAP);
}

vec4 wrap(vec4 v) {
  return v - WRAP * floor(v / WRAP);
}

vec3 smooth(vec3 v) {
  return v*v*v*(3.0 * v * (2.0 * v - 5.0) + 10.0);
}

vec4 shuffle(vec4 v) {
  vec4 f = (v * (SHFL * v + 1.0)) / WRAP;
  return -WRAP * floor(f) + SHFL * v * v + v;
}

////////////////////////////////////////////////////////////////////////////////

vec4 color_px(float val, float p) {
  const float p1 = 0.40;
  const float p2 = 0.50;
  const float p3 = 0.60;

  vec4 col = vec4(0.0, 0.0, 0.0, 1.0);
  float v = S(val, 0.0, 1.0);
  if (v <= -0.00001) {
    col[0] = 0.0;
    col[1] = 0.0;
    col[2] = 0.0;
  } else if (v < p1) {
    float t2 = INT(v, 0.0, p1);
    float t1 = 1.0 - t2;
    col[0] = t1 * c11 + t2 * c21;
    col[1] = t1 * c12 + t2 * c22;
    col[2] = t1 * c13 + t2 * c23;
  } else if (v < p2) {
    float t2 = INT(v, p1, p2);
    float t1 = 1.0 - t2;
    col[0] = t1 * c21 + t2 * c31;
    col[1] = t1 * c22 + t2 * c32;
    col[2] = t1 * c23 + t2 * c33;
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

////////////////////////////////////////////////////////////////////////////////

float gnoise(vec3 P) {
  vec3 Pi0 = floor(P); // Integer part for indexing
  vec3 Pi1 = Pi0 + vec3(1.0); // Integer part + 1
  Pi0 = wrap(Pi0);
  Pi1 = wrap(Pi1);
  vec3 Pf0 = fract(P); // Fractional part for interpolation
  vec3 Pf1 = Pf0 - vec3(1.0); // Fractional part - 1.0
  vec4 ix = vec4(Pi0.x, Pi1.x, Pi0.x, Pi1.x);
  vec4 iy = vec4(Pi0.yy, Pi1.yy);
  vec4 iz0 = Pi0.zzzz;
  vec4 iz1 = Pi1.zzzz;

  vec4 ixy = shuffle(shuffle(ix) + iy);
  vec4 ixy0 = shuffle(ixy + iz0);
  vec4 ixy1 = shuffle(ixy + iz1);

  vec4 gx0 = ixy0 * (1.0 / 7.0);
  vec4 gy0 = fract(floor(gx0) * (1.0 / 7.0)) - 0.5;
  gx0 = fract(gx0);
  vec4 gz0 = vec4(0.5) - abs(gx0) - abs(gy0);
  vec4 sz0 = step(gz0, vec4(0.0));
  gx0 -= sz0 * (step(0.0, gx0) - 0.5);
  gy0 -= sz0 * (step(0.0, gy0) - 0.5);

  vec4 gx1 = ixy1 * (1.0 / 7.0);
  vec4 gy1 = fract(floor(gx1) * (1.0 / 7.0)) - 0.5;
  gx1 = fract(gx1);
  vec4 gz1 = vec4(0.5) - abs(gx1) - abs(gy1);
  vec4 sz1 = step(gz1, vec4(0.0));
  gx1 -= sz1 * (step(0.0, gx1) - 0.5);
  gy1 -= sz1 * (step(0.0, gy1) - 0.5);

  vec3 g000 = vec3(gx0.x,gy0.x,gz0.x);
  vec3 g100 = vec3(gx0.y,gy0.y,gz0.y);
  vec3 g010 = vec3(gx0.z,gy0.z,gz0.z);
  vec3 g110 = vec3(gx0.w,gy0.w,gz0.w);
  vec3 g001 = vec3(gx1.x,gy1.x,gz1.x);
  vec3 g101 = vec3(gx1.y,gy1.y,gz1.y);
  vec3 g011 = vec3(gx1.z,gy1.z,gz1.z);
  vec3 g111 = vec3(gx1.w,gy1.w,gz1.w);

  vec4 norm0 = normalize(vec4(dot(g000, g000), dot(g010, g010), dot(g100, g100), dot(g110, g110)));
  g000 *= norm0.x;
  g010 *= norm0.y;
  g100 *= norm0.z;
  g110 *= norm0.w;
  vec4 norm1 = normalize(vec4(dot(g001, g001), dot(g011, g011), dot(g101, g101), dot(g111, g111)));
  g001 *= norm1.x;
  g011 *= norm1.y;
  g101 *= norm1.z;
  g111 *= norm1.w;

  float n000 = dot(g000, Pf0);
  float n100 = dot(g100, vec3(Pf1.x, Pf0.yz));
  float n010 = dot(g010, vec3(Pf0.x, Pf1.y, Pf0.z));
  float n110 = dot(g110, vec3(Pf1.xy, Pf0.z));
  float n001 = dot(g001, vec3(Pf0.xy, Pf1.z));
  float n101 = dot(g101, vec3(Pf1.x, Pf0.y, Pf1.z));
  float n011 = dot(g011, vec3(Pf0.x, Pf1.yz));
  float n111 = dot(g111, Pf1);

  vec3 fade_xyz = smooth(Pf0);
  vec4 n_z = mix(vec4(n000, n100, n010, n110), vec4(n001, n101, n011, n111), fade_xyz.z);
  vec2 n_yz = mix(n_z.xy, n_z.zw, fade_xyz.y);
  float n_xyz = mix(n_yz.x, n_yz.y, fade_xyz.x); 
  return 2.2 * n_xyz;
}

vec4 taylorInvSqrt( vec4 r ) {
  return 1.79284291400159 - 0.85373472095314 * r;
}

float snoise( vec3 v ) {

  const vec2 C = vec2( 1.0 / 6.0, 1.0 / 3.0 );
  const vec4 D = vec4( 0.0, 0.5, 1.0, 2.0 );

  // First corner

  vec3 i  = floor( v + dot( v, C.yyy ) );
  vec3 x0 = v - i + dot( i, C.xxx );

  // Other corners

  vec3 g = step( x0.yzx, x0.xyz );
  vec3 l = 1.0 - g;
  vec3 i1 = min( g.xyz, l.zxy );
  vec3 i2 = max( g.xyz, l.zxy );

  vec3 x1 = x0 - i1 + 1.0 * C.xxx;
  vec3 x2 = x0 - i2 + 2.0 * C.xxx;
  vec3 x3 = x0 - 1. + 3.0 * C.xxx;

  // Permutations

  i = mod( i, 289.0 );
  vec4 p = shuffle( shuffle( shuffle(
    i.z + vec4( 0.0, i1.z, i2.z, 1.0 ) )
  + i.y + vec4( 0.0, i1.y, i2.y, 1.0 ) )
  + i.x + vec4( 0.0, i1.x, i2.x, 1.0 ) );

  // Gradients
  // ( N*N points uniformly over a square, mapped onto an octahedron.)

  float n_ = 1.0 / 7.0; // N=7

  vec3 ns = n_ * D.wyz - D.xzx;

  vec4 j = p - 49.0 * floor( p * ns.z *ns.z );  //  mod(p,N*N)

  vec4 x_ = floor( j * ns.z );
  vec4 y_ = floor( j - 7.0 * x_ );    // mod(j,N)

  vec4 x = x_ *ns.x + ns.yyyy;
  vec4 y = y_ *ns.x + ns.yyyy;
  vec4 h = 1.0 - abs( x ) - abs( y );

  vec4 b0 = vec4( x.xy, y.xy );
  vec4 b1 = vec4( x.zw, y.zw );


  vec4 s0 = floor( b0 ) * 2.0 + 1.0;
  vec4 s1 = floor( b1 ) * 2.0 + 1.0;
  vec4 sh = -step( h, vec4( 0.0 ) );

  vec4 a0 = b0.xzyw + s0.xzyw * sh.xxyy;
  vec4 a1 = b1.xzyw + s1.xzyw * sh.zzww;

  vec3 p0 = vec3( a0.xy, h.x );
  vec3 p1 = vec3( a0.zw, h.y );
  vec3 p2 = vec3( a1.xy, h.z );
  vec3 p3 = vec3( a1.zw, h.w );

  // Normalise gradients

  vec4 norm = taylorInvSqrt( vec4( dot( p0, p0 ), dot( p1, p1 ), dot( p2, p2 ), dot( p3, p3 ) ) );
  p0 *= norm.x;
  p1 *= norm.y;
  p2 *= norm.z;
  p3 *= norm.w;

  // Mix final noise value

  vec4 m = max( 0.6 - vec4( dot( x0, x0 ), dot( x1, x1 ), dot( x2, x2 ), dot( x3, x3 ) ), 0.0 );
  m = m * m;
  return 42.0 * dot( m*m, vec4( dot( p0, x0 ), dot( p1, x1 ),
    dot( p2, x2 ), dot( p3, x3 ) ) );

}

////////////////////////////////////////////////////////////////////////////////

#define OCTAVES 32

float perlin_noise(vec3 P) {
  float n = 0.0;
  float div = 1.0;
  float mul = 1.0;

  for (int i = 0; i < OCTAVES; i++) {
    div /= 2.0;
    mul *= 2.0;
    n+= div * abs(snoise(P*mul));
  }

  // n += 1.0 * abs( gnoise( P ) );
  // n += 0.5 * abs( gnoise( P * 2.0 ) );
  // n += 0.25 * abs( gnoise( P * 4.0 ) );
  // n += 0.125 * abs( gnoise( P * 8.0 ) );

  float rn = 1.0 - n;

  return rn * rn;
}

////////////////////////////////////////////////////////////////////////////////

void main(void) {
  float noise = perlin_noise(vec3(aspect*pos.x + p, pos.y + p, p));
  vec4 color = color_px(noise, p);
  gl_FragColor = color;
}

// ////////////////////////////////////////////////////////////////////////////////

// const int P_MASK = 255;
// const int P_SIZE = 256;

// ////////////////////////////////////////////////////////////////////////////////

// const int G_MASK    = 15;
// const int G_SIZE    = 16;
// const int G_VECSIZE =  4;

// ////////////////////////////////////////////////////////////////////////////////

// int randn(int i) {
//   return int(mod(float(1103515245 * i + 12345), 256.0));
// }

// ////////////////////////////////////////////////////////////////////////////////

// //int mod(int x, int a)
// //{
// //    int n = (x / a);
// //    int v = v - n * a;
// //    if ( v < 0 )
// //        v += a;
// //    return v;   
// //}
 
// float smooth(float t)
// {
//     return t*t*t*(t*(t*6.0-15.0)+10.0); 
// }
 
// vec4 normalized(vec4 v)
// {
//     float d = sqrt(v.x * v.x + v.y * v.y + v.z * v.z);
//     d = d > 0.0 ? d : 1.0;
//     vec4 result = vec4(v.x, v.y, v.z, 0.0) / d;
//     //result.w = 1.0;
//     return result;
// }

// vec4 project(vec4 v, vec4 u)
// {
//     return dot(u, v) / dot(u, u) * u;
// }

// vec4 orthonormalize(vec4 v1, vec4 v2)
// {
//     return normalize(v2 - project(v2, v1));
// }

// ////////////////////////////////////////////////////////////////////////////////

// float mix1d(float a, float b, float t)
// {
//     float ba = b - a;
//     float tba = t * ba;
//     float atba = a + tba;
//     return atba;    
// }
 
// vec2 mix2d(vec2 a, vec2 b, float t)
// {
//     vec2 ba = b - a;
//     vec2 tba = t * ba;
//     vec2 atba = a + tba;
//     return atba;    
// }
 
// vec4 mix3d(vec4 a, vec4 b, float t)
// {
//     vec4 ba = b - a;
//     vec4 tba = t * ba;
//     vec4 atba = a + tba;
//     return atba;    
// }

// //vec4 mix4d(vec4 a, vec4 b, float t)
// //{
// //    vec4 ba = b - a;
// //    vec4 tba = t * ba;
// //    vec4 atba = a + tba;
// //    return atba;    
// //}

// ////////////////////////////////////////////////////////////////////////////////
// // Lattice points
// ////////////////////////////////////////////////////////////////////////////////
 
// int lattice1d(int i)
// {
//     return P[i];
// }
 
// int lattice2d(ivec2 i)
// {
//     return P[i.x + P[i.y]];
// }
 
// int lattice3d(ivec4 i)
// {
//     return P[i.x + P[i.y + P[i.z]]];
// }

// //int lattice4d(ivec4 i)
// //{
// //    return P[i.x + P[i.y + P[i.z + P[i.w]]]];
// //}

// ////////////////////////////////////////////////////////////////////////////////
// // Gradients
// ////////////////////////////////////////////////////////////////////////////////

// float gradient1d(int i, float v)
// {
//     int index = int(mod(float(lattice1d(i)), float(G_SIZE))) * G_VECSIZE;
//     float g = G[index + 0];
//     return (v * g);
// }

// float gradient2d(ivec2 i, vec2 v)
// {
//     int index = int(mod(float(lattice2d(i)), float(G_SIZE))) * G_VECSIZE;
//     vec2 g = vec2(G[index + 0], G[index + 1]);
//     return dot(v, g);
// }
 
// float gradient3d(ivec4 i, vec4 v)
// {
//     int index = int(mod(float(lattice3d(i)), float(G_SIZE))) * G_VECSIZE;
//     vec4 g = vec4(G[index + 0], G[index + 1], G[index + 2], 1.0);
//     return dot(v, g);
// }

// //float gradient4d(ivec4 i, vec4 v)
// //{
// //    int index = (lattice4d(i) & G_MASK) * G_VECSIZE;
// //    vec4 g = (vec4)(G[index + 0], G[index + 1], G[index + 2], G[index + 3]);
// //    return dot(v, g);
// //}

// ////////////////////////////////////////////////////////////////////////////////
// // Signed gradient noise
// ////////////////////////////////////////////////////////////////////////////////

// float sgnoise1d(float position)
// {
//     float p = position;
//     float pf = floor(p);
//     int ip = int(pf);
//     float fp = p - pf;        
//     ip = int(mod(float(ip), float(P_MASK+1)));
    
//     float n0 = gradient1d(ip + 0, fp - 0.0);
//     float n1 = gradient1d(ip + 1, fp - 1.0);
 
//     float n = mix1d(n0, n1, smooth(fp));
//     return n * (1.0 / 0.7);
// }
 
// float sgnoise2d(vec2 position)
// {
//     vec2 p = position;
//     vec2 pf = floor(p);
//     ivec2 ip = ivec2(int(pf.x), int(pf.y));
//     vec2 fp = p - pf;        
//     ip = ivec2(mod(float(ip), float(P_MASK+1)));
    
//     const ivec2 I00 = ivec2(0, 0);
//     const ivec2 I01 = ivec2(0, 1);
//     const ivec2 I10 = ivec2(1, 0);
//     const ivec2 I11 = ivec2(1, 1);
    
//     const vec2 F00 = vec2(0.0, 0.0);
//     const vec2 F01 = vec2(0.0, 1.0);
//     const vec2 F10 = vec2(1.0, 0.0);
//     const vec2 F11 = vec2(1.0, 1.0);
 
//     float n00 = gradient2d(ip + I00, fp - F00);
//     float n10 = gradient2d(ip + I10, fp - F10);
//     float n01 = gradient2d(ip + I01, fp - F01);
//     float n11 = gradient2d(ip + I11, fp - F11);
 
//     vec2 n0001 = vec2(n00, n01);
//     vec2 n1011 = vec2(n10, n11);
 
//     vec2 n2 = mix2d(n0001, n1011, smooth(fp.x));
//     float n = mix1d(n2.x, n2.y, smooth(fp.y));
//     return n * (1.0 / 0.7);
// }
 
// float sgnoise3d(vec4 position)
// {
 
//     vec4 p = position;
//     vec4 pf = floor(p);
//     ivec4 ip = ivec4(int(pf.x), int(pf.y), int(pf.z), 0.0);
//     vec4 fp = p - pf;        
//     ip = ivec4(mod(float(ip), float(P_MASK+1)));
 
//     ivec4 I000 = ivec4(0, 0, 0, 0);
//     ivec4 I001 = ivec4(0, 0, 1, 0);  
//     ivec4 I010 = ivec4(0, 1, 0, 0);
//     ivec4 I011 = ivec4(0, 1, 1, 0);
//     ivec4 I100 = ivec4(1, 0, 0, 0);
//     ivec4 I101 = ivec4(1, 0, 1, 0);
//     ivec4 I110 = ivec4(1, 1, 0, 0);
//     ivec4 I111 = ivec4(1, 1, 1, 0);
    
//     vec4 F000 = vec4(0.0, 0.0, 0.0, 0.0);
//     vec4 F001 = vec4(0.0, 0.0, 1.0, 0.0);
//     vec4 F010 = vec4(0.0, 1.0, 0.0, 0.0);
//     vec4 F011 = vec4(0.0, 1.0, 1.0, 0.0);
//     vec4 F100 = vec4(1.0, 0.0, 0.0, 0.0);
//     vec4 F101 = vec4(1.0, 0.0, 1.0, 0.0);
//     vec4 F110 = vec4(1.0, 1.0, 0.0, 0.0);
//     vec4 F111 = vec4(1.0, 1.0, 1.0, 0.0);
    
//     float n000 = gradient3d(ip + I000, fp - F000);
//     float n001 = gradient3d(ip + I001, fp - F001);
    
//     float n010 = gradient3d(ip + I010, fp - F010);
//     float n011 = gradient3d(ip + I011, fp - F011);
    
//     float n100 = gradient3d(ip + I100, fp - F100);
//     float n101 = gradient3d(ip + I101, fp - F101);
 
//     float n110 = gradient3d(ip + I110, fp - F110);
//     float n111 = gradient3d(ip + I111, fp - F111);
 
//     vec4 n40 = vec4(n000, n001, n010, n011);
//     vec4 n41 = vec4(n100, n101, n110, n111);
 
//     vec4 n4 = mix3d(n40, n41, smooth(fp.x));
//     vec2 n2 = mix2d(n4.xy, n4.zw, smooth(fp.y));
//     float n = mix1d(n2.x, n2.y, smooth(fp.z));
//     return n * (1.0 / 0.7);
// }


// ////////////////////////////////////////////////////////////////////////////////
// // Unsigned gradient noise
// ////////////////////////////////////////////////////////////////////////////////
 
// float ugnoise1d(float position)
// {
//     return (0.5 - 0.5 * sgnoise1d(position));
// }

// float ugnoise2d(vec2 position)
// {
//     return (0.5 - 0.5 * sgnoise2d(position));
// }

// float ugnoise3d(vec4 position)
// {
//     return (0.5 - 0.5 * sgnoise3d(position));
// }
 
// ////////////////////////////////////////////////////////////////////////////////

// float remainder(float x, float y) {
//   return x - y * floor(x / y);
// }

// ////////////////////////////////////////////////////////////////////////////////

// float turbulence3d(
//     vec4 position, 
//     float frequency,
//     float lacunarity, 
//     float increment, 
//     float octaves)
// {
//     int i = 0;
//     float fi = 0.0;
//     float remainder = 0.0; 
//     float sample = 0.0;    
//     float value = 0.0;
//     int iterations = int(octaves);
    
//     for (i = 0; i < iterations; i++)
//     {
//         fi = float(i);
//         sample = (1.0 - 2.0 * sgnoise3d(position * frequency));
//         sample *= pow( lacunarity, -fi * increment );
//         value += abs(sample);
//         frequency *= lacunarity;
//     }
    
//     remainder = octaves - float(iterations);
//     if ( remainder > 0.0 )
//     {
//         sample = remainder * (1.0 - 2.0 * sgnoise3d(position * frequency));
//         sample *= pow( lacunarity, -fi * increment );
//         value += abs(sample);
//     }
        
//     return value;   
// }

// ////////////////////////////////////////////////////////////////////////////////

// float MakeInt32Range(float value)
// {
//     if (value >= 1073741824.0) 
//     {
//         return (2.0 * remainder(value, 1073741824.0)) - 1073741824.0; 
//     }
//     else if (value <= -1073741824.0) 
//     {
//         return (2.0 * remainder(value, 1073741824.0)) + 1073741824.0;
//     }
//     else
//     {
//         return value;
//     }
    
// }

// float GradientCoherentNoise3D(float x, float y, float z, int seed)
// {
//     float s = float(seed);
//     vec4 pos = vec4(x+s, y+s, z+s, 0.0);
    
//     return sgnoise3d(pos);
// }

// float Perlin(float x, float y, float z, 
//     float frequency, float lacunarity, float persistence,
//     int octaves, int seed)
// {
//     seed = seed + 0;
    
//     float value = 0.0;
//     float signal = 0.0;
//     float cp = 1.0;
    
//     x *= frequency;
//     y *= frequency;
//     z *= frequency;
//     for (int i = 0; i < octaves; i++)
//     {
//         float nx = MakeInt32Range(x);
//         float ny = MakeInt32Range(y);
//         float nz = MakeInt32Range(z);
//         seed = seed + i;
//         signal = GradientCoherentNoise3D(nx, ny, nz, seed);
//         value += signal * cp;
//         x *= lacunarity;
//         y *= lacunarity;
//         z *= lacunarity;
//         cp *= persistence;
//     }
//     return value;
// }

// float RidgedMultifractal(float x, float y, float z, 
//     float frequency, float lacunarity, int octaves, 
//     int seed)
// {
    
//     x *= frequency;
//     y *= frequency;
//     z *= frequency;
    
//     float signal = 0.0;
//     float value = 0.0;
//     float weight = 1.0;
//     float offset = 1.0;
//     float gain = 2.0;
//     float f = 1.0;
    
//     for(int i = 0; i < octaves; i++)
//     {
//         float nx = MakeInt32Range(x);
//         float ny = MakeInt32Range(y);
//         float nz = MakeInt32Range(z);
//         seed = seed + i;
//         signal = GradientCoherentNoise3D(nx, ny, nz, seed);
//         signal = abs(signal);
//         signal = offset - signal;
//         signal *= signal;
//         signal *= weight;
//         weight = signal * gain;
//         if (weight > 1.0) { weight = 1.0; }
//         if (weight < 0.0) { weight = 0.0; }
//         value += (signal * pow(f, -1.0));
//         f *= lacunarity;
//         x *= lacunarity;
//         y *= lacunarity;
//         z *= lacunarity;
//     }
    
//     return (value * 1.25) - 1.0;
// }

// float Billow(float x, float y, float z, 
//     float frequency, float lacunarity, float persistence,
//     int octaves, int seed)
// {
//     float value = 0.0;
//     float signal = 0.0;
//     float curp = 1.0;
//     float nx, ny, nz;
//     x *= frequency;
//     y *= frequency;
//     z *= frequency;
//     for(int i = 0; i < octaves; i++)
//     {
//         nx = MakeInt32Range(x);
//         ny = MakeInt32Range(y);
//         nz = MakeInt32Range(z);
//         seed = seed + i;
//         signal = GradientCoherentNoise3D(nx, ny, nz, seed);
//         signal = 2.0 * abs(signal) - 1.0;
//         value += signal * curp;
//         x *= lacunarity;
//         y *= lacunarity;
//         z *= lacunarity;
//         curp *= persistence;
//     }

//     return value + 0.5;
// }

// float ScaleBias(float value, float scale, float bias)
// {
//     return value * scale + bias;
// }

// float MapCubicSCurve(float value)
// {
//     return (value * value * (3.0 - 2.0 * value));
// }

// float InterpolateLinear(float a, float b, float position)
// {
//     return ((1.0 - position) * a) + (position * b);
// }

// float Select(float value1, float value2, float selector, 
//     float selectMin, float selectMax, float fallOff)
// {
//     float cv = selector;
//     if (fallOff > 0.0)
//     {
//         if (cv < (selectMin - fallOff)) { return value1; }
//         else if (cv < (selectMin + fallOff))
//         {
//             float lc = (selectMin - fallOff);
//             float uc = (selectMin + fallOff);
//             float a = MapCubicSCurve((cv - lc) / (uc - lc));
//             return InterpolateLinear(value1, value2, a);

//         }
//         else if (cv < (selectMax - fallOff)) { return value2; }
//         else if (cv < (selectMax + fallOff))
//         {
//             float lc = (selectMax - fallOff);
//             float uc = (selectMax + fallOff);
//             float a = MapCubicSCurve((cv - lc) / (uc - lc));
//             return InterpolateLinear(value2, value1, a);

//         }
//         return value1;
//     }
//     else
//     {
//         if (cv < selectMin || cv > selectMax) { return value1; }
//         return value2;
//     }
// }

// vec4 TurbulenceShift(
//     float x, float y, float z,
//     float power, float frequency, 
//     int octaves, int seed)
// {
//     float X0 = (12414.0 / 65536.0);
//     float Y0 = (65124.0 / 65536.0);
//     float Z0 = (31337.0 / 65536.0);
//     float X1 = (26519.0 / 65536.0);
//     float Y1 = (18128.0 / 65536.0);
//     float Z1 = (60493.0 / 65536.0);
//     float X2 = (53820.0 / 65536.0);
//     float Y2 = (11213.0 / 65536.0);
//     float Z2 = (44845.0 / 65536.0);
    
//     float xD = Perlin(x+X0, y+Y0, z+Z0, frequency, 2.0, 0.5, octaves, seed+0);
//     float yD = Perlin(x+X1, y+Y1, z+Z1, frequency, 2.0, 0.5, octaves, seed+1);
//     float zD = Perlin(x+X2, y+Y2, z+Z2, frequency, 2.0, 0.5, octaves, seed+2);
    
//     float xd = x + power * xD;
//     float yd = y + power * yD;
//     float zd = z + power * zD;
//     return vec4(xd, yd, zd, 0.0);
// }

// ////////////////////////////////////////////////////////////////////////////////



// vec4 color_px(float val, float p) {
//   const float p1 = 0.00;
//   const float p2 = 0.50;
//   const float p3 = 0.90;

//   float t = 0.5 * (sin(4.0 * p) + 1.0);

//   vec4 col = vec4(0.0, 0.0, 0.0, 1.0);
//   float v = S(val, 0.0, 1.0);
//   if (v <= -0.00001) {
//     col[0] = 0.0;
//     col[1] = 0.0;
//     col[2] = 0.0;
//   } else if (v < p1) {
//     float t2 = INT(v, 0.0, p1);
//     float t1 = 1.0 - t2;
//     col[0] = t1 * c11 + t2 * (t*c21+(1.0-t)*cr1);
//     col[1] = t1 * c12 + t2 * (t*c22+(1.0-t)*cr2);
//     col[2] = t1 * c13 + t2 * (t*c23+(1.0-t)*cr3);
//   } else if (v < p2) {
//     float t2 = INT(v, p1, p2);
//     float t1 = 1.0 - t2;
//     col[0] = t1 * (t*c21+(1.0-t)*cr1) + t2 * c31;
//     col[1] = t1 * (t*c22+(1.0-t)*cr2) + t2 * c32;
//     col[2] = t1 * (t*c23+(1.0-t)*cr3) + t2 * c33;
//   } else if (v < p3) {
//     float t2 = INT(v, p2, p3);
//     float t1 = 1.0 - t2;
//     col[0] = t1 * c31 + t2 * c41;
//     col[1] = t1 * c32 + t2 * c42;
//     col[2] = t1 * c33 + t2 * c43;
//   } else {
//     float t2 = INT(v, p3, 1.0);
//     float t1 = 1.0 - t2;
//     col[0] = t1 * c41 + t2 * c51;
//     col[1] = t1 * c42 + t2 * c52;
//     col[2] = t1 * c43 + t2 * c53;
//   }

//   return col;
// }

// void main(void) {
//   float d = float(order);
//   float sum = 0.0;
//   float dX = 0.5 * p;
//   float dY = 0.4 * p;
//   float s = SCALE * (sin(p) + 1.5) + float(5*order);

//   // float x = pos.x + dX;
//   // float y = pos.y + dY;

//   float x = dX + aspect * pos.x * cos(p) - pos.y * sin(p);
//   float y = dY + pos.y * cos(p) + aspect * pos.x * sin(p);

//   for (int k = 0; k < 30; k++) {
//     if (k < order) {
//       sum += cos(s * x * cos(float(k) * PI / d) - 
//                  s * y * sin(float(k) * PI / d) + 40.0*p);
//     }
//   }
//   sum *= MAG;
//   sum = atan(sum) / (1.0 * PI) + 0.5;

//   // vec4 color = vec4(sum, sum, sum, 1.0);
//   vec4 color = color_px(sum, p);

//   gl_FragColor = color;
// }