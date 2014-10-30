// vectors.h - vector stuff
// Copyright (C) 2014 Richard Hennigan

#ifndef MATH_VECTORS_H_
#define MATH_VECTORS_H_

#include <stdlib.h>
#include <stdbool.h>
#include "./utils.h"

typedef enum comp_stat_e {
  C_UNSET,
  C_DISP,
  C_ZERO,
  C_NONZERO
} comp_stat;

typedef struct vector64_s {
  int dim;
  double* c;
  comp_stat cstat;
} vector64_t;

typedef struct vector32_s {
  int dim;
  float* c;
  comp_stat cstat;
} vector32_t;

typedef vector64_t vector_t;

vector_t vec_add(vector_t a, vector_t b);
void     vec_add_i(vector_t * a, vector_t b);
void     vec_check1(vector_t * a, const char * f);
void     vec_check2(vector_t * a, vector_t * b, const char * f);
vector_t vec_copy(vector_t a);
char *   vec_cstat(vector_t a);
vector_t vec_cross(vector_t a, vector_t b);
void     vec_dispose(vector_t * a);
double   vec_dist(vector_t a, vector_t b);
double   vec_dot(vector_t a, vector_t b);
vector_t vec_init(int dim);
vector_t vec_mul_c(vector_t a, vector_t b);
vector_t vec_mul_s(double s, vector_t a);
void     vec_mul_s_i(double s, vector_t * a);
vector_t vec_neg(vector_t a);
vector_t vec_new(int dim, ... /* va double */);
double   vec_norm(vector_t a);
vector_t vec_normalize(vector_t a);
void     vec_normalize_i(vector_t * a);
void     vec_print(vector_t a);
vector_t vec_rand(int dim, double low, double high);
vector_t vec_sub(vector_t a, vector_t b);
char *   vec_tostring(vector_t a);
vector_t vec_zero(int dim);

#endif  // MATH_VECTORS_H_
