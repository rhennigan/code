// matrices.h - matrix stuff
// Copyright (C) 2014 Richard Hennigan

#ifndef MATH_MATRICES_H_
#define MATH_MATRICES_H_

#include "./vectors.h"

typedef struct matrix64_s {
  int rows, cols;
  vector64_t * r;
} matrix64_t;

typedef struct matrix32_s {
  int rows, cols;
  vector32_t * r;
} matrix32_t;

typedef matrix64_t matrix_t;

matrix_t mat_add(matrix_t m1, matrix_t m2);
void     mat_add_i(matrix_t * m1, matrix_t m2);
void     mat_dispose(matrix_t * m);
vector_t mat_dotvr(matrix_t m, vector_t v);
void     mat_export(matrix_t m, const char * filename);
double   mat_get(matrix_t m, int row, int col);
vector_t mat_getc(matrix_t m, int col);
vector_t mat_getr(matrix_t m, int row);
matrix_t mat_init(int rows, int cols);
vector_t mat_mean(matrix_t m);
matrix_t mat_mul(matrix_t m1, matrix_t m2);
matrix_t mat_new(int rows, int cols, ... /* va vector_t */);
// TODO(rhennigan): move principal axis stuff to a new file
vector_t mat_principal_axis(matrix_t m);
void     mat_print(matrix_t m, int indent);
matrix_t mat_rand(int rows, int cols, double low, double high);
matrix_t mat_shift(matrix_t m);
vector_t mat_sum(matrix_t m);
char *   mat_tostring(matrix_t m);
matrix_t mat_transpose(matrix_t m);
matrix_t mat_zero(int rows, int cols);

#endif  // MATH_MATRICES_H_
