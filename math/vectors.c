// vectors.c - vector stuff
// Copyright (C) 2014 Richard Hennigan

#include <stdarg.h>
#include <assert.h>
#include <stdio.h>
#include <math.h>
#include <stdbool.h>
#include "./vectors.h"
#include "./utils.h"

#define _DEBUG_ true
#define _PPREC_ "3"
#define _SPREC_ "3"

vector_t vec_add(vector_t a, vector_t b) {
  if (_DEBUG_) vec_check2(&a, &b, "vec_add");
  vector_t c = vec_init(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    c.comp[i] = a.comp[i] + b.comp[i];
  }
  return c;
}

void vec_add_i(vector_t * a, vector_t b) {
  if (_DEBUG_) vec_check2(a, &b, "vec_addi");
  int i;
  for (i = 0; i < a->dim; i++) {
    a->comp[i] += b.comp[i];
  }
}

void vec_check1(vector_t * a, const char * f) {
  check_fail(a == NULL,          f, "vector is NULL");
  check_fail(a->cstat == C_DISP, f, "vector has been disposed");
  check_fail(a->comp == NULL,    f, "vector components are NULL");
  a->cstat = C_ZERO;
  int i;
  for (i = 0; i < a->dim; i++) {
    if (a->comp[i] != 0.0) {
      a->cstat = C_NONZERO;
      break;
    }
  }
}

void vec_check2(vector_t * a, vector_t * b, const char * f) {
  vec_check1(a, f);
  vec_check1(b, f);
  check_fail(a->dim != b->dim, f, "vectors have different dimensions");
}

vector_t vec_copy(vector_t a) {
  if (_DEBUG_) vec_check1(&a, "vec_copy");
  vector_t b = vec_init(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    b.comp[i] = a.comp[i];
  }
  return b;
}

char * vec_cstat(vector_t a) {
  if (_DEBUG_) vec_check1(&a, "vec_cstat");
  char * str = malloc(BUFSIZ);
  switch (a.cstat) {
    case C_UNSET:
      str = "C_UNSET";
      break;
    case C_DISP:
      str = "C_DISP";
      break;
    case C_ZERO:
      str = "C_ZERO";
      break;
    case C_NONZERO:
      str = "C_NONZERO";
      break;
    default:
      str = "UNKNOWN";
      break;
  }
  return str;
}

vector_t vec_cross(vector_t a, vector_t b) {
  if (_DEBUG_) {
    vec_check2(&a, &b, "vec_cross");
    check_fail(a.dim == 3 && b.dim == 3, "vec_cross",
               "cross product only defined for 3 dimensions");
  }
  vector_t c = vec_init(a.dim);
  c.comp[0] = a.comp[1] * b.comp[2] - a.comp[2] * b.comp[1];
  c.comp[1] = a.comp[2] * b.comp[0] - a.comp[0] * b.comp[2];
  c.comp[2] = a.comp[0] * b.comp[1] - a.comp[1] * b.comp[0];
  return c;
}

void vec_dispose(vector_t * a) {
  if (_DEBUG_) check_fail(a != NULL && a->cstat != C_DISP, "vec_dispose",
                          "vector components have already been disposed");
  free(a->comp);
  a->comp = NULL;
  a->dim = -1;
  a->cstat = C_DISP;
}

double vec_dist(vector_t a, vector_t b) {
  if (_DEBUG_) vec_check2(&a, &b, "vec_dist");
  return vec_norm(vec_sub(a, b));
}

double vec_dot(vector_t a, vector_t b) {
  if (_DEBUG_) vec_check2(&a, &b, "vec_dot");
  double dot;
  int i;
  for (i = 0; i < a.dim; i++) {
    dot += a.comp[i] * b.comp[i];
  }
  return dot;
}

vector_t vec_init(int dim) {
  if (_DEBUG_) check_fail(dim < 1, "vec_init", "invalid dimension");
  vector_t a;
  a.comp = malloc(sizeof(double) * dim);
  if (_DEBUG_) check_fail(a.comp == NULL, "vec_init",
                          "unable to allocate memory");
  a.dim = dim;
  a.cstat = C_UNSET;
  return a;
}

vector_t vec_mul_c(vector_t a, vector_t b) {
  if (_DEBUG_) vec_check2(&a, &b, "vec_mul_c");
  vector_t c = vec_init(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    c.comp[i] = a.comp[i] * b.comp[i];
  }
  return c;
}

vector_t vec_mul_s(double s, vector_t a) {
  if (_DEBUG_) vec_check1(&a, "vec_mul_s");
  vector_t b = vec_init(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    b.comp[i] = s * a.comp[i];
  }
  return b;
}

void vec_mul_s_i(double s, vector_t * a) {
  if (_DEBUG_) vec_check1(a, "vec_mul_s_i");
  int i;
  for (i = 0; i < a->dim; i++) {
    a->comp[i] *= s;
  }
}

vector_t vec_neg(vector_t a) {
  if (_DEBUG_) vec_check1(&a, "vec_neg");
  vector_t b = vec_init(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    b.comp[i] = -a.comp[i];
  }
  return b;
}

vector_t vec_new(int dim, ...) {
  if (_DEBUG_) check_fail(dim < 1, "vec_new", "invalid dimension");
  va_list argp;
  va_start(argp, dim);
  vector_t a = vec_init(dim);
  int i;
  for (i = 0; i < dim; i++) {
    a.comp[i] = va_arg(argp, double);
  }
  va_end(argp);
  return a;
}

double vec_norm(vector_t a) {
  if (_DEBUG_) vec_check1(&a, "vec_norm");
  return sqrt(vec_dot(a, a));
}

vector_t vec_normalize(vector_t a) {
  if (_DEBUG_) vec_check1(&a, "vec_normalize");
  return vec_mul_s(1.0 / vec_norm(a), a);
}

void vec_normalize_i(vector_t * a) {
  if (_DEBUG_) vec_check1(a, "vec_normalize_i");
  vec_mul_s_i(1.0 / vec_norm((*a)), a);
}

void vec_print(vector_t a) {
  if (_DEBUG_) vec_check1(&a, "vec_print");
  printf("(");
  int i;
  for (i = 0; i < a.dim - 1; i++) {
    printf("%."_PPREC_"f, ", a.comp[i]);
  }
  printf("%."_PPREC_"f)", a.comp[i]);
}

vector_t vec_sub(vector_t a, vector_t b) {
  if (_DEBUG_) vec_check2(&a, &b, "vec_sub");
  return vec_add(a, vec_neg(b));
}

char * vec_tostring(vector_t a) {
  if (_DEBUG_) vec_check1(&a, "vec_tostring");
  char * str = malloc(BUFSIZ);
  char * ptr = str;
  int n;
  n = snprintf(ptr, BUFSIZ, "(");
  int i;
  for (i = 0; i < a.dim - 1; i++) {
    ptr += n;
    n = snprintf(ptr, BUFSIZ, "%."_SPREC_"f, ", a.comp[i]);
  }
  ptr += n;
  snprintf(ptr, BUFSIZ, "%."_SPREC_"f)", a.comp[i]);
  return str;
}

vector_t vec_zero(int dim) {
  if (_DEBUG_) check_fail(dim < 1, "vec_zero", "invalid dimension");
  vector_t a = vec_init(dim);
  int i;
  for (i = 0; i < dim; i++) {
    a.comp[i] = 0.0;
  }
  a.cstat = C_ZERO;
  return a;
}
