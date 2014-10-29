// matrices.c - matrix stuff
// Copyright (C) 2014 Richard Hennigan

#include <stdarg.h>
#include <stdio.h>
#include "./vectors.h"
#include "./matrices.h"
#include "./utils.h"

#define _DEBUG_ true
#define _PA_ITERATIONS_ 5

matrix_t mat_add(matrix_t m1, matrix_t m2) {
  if (_DEBUG_) check_fail(m1.cols == m2.cols && m1.rows == m2.rows, "mat_add",
                          "matrices must have the same dimensions");
  matrix_t m3 = mat_init(m1.rows, m1.cols);
  int i;
  for (i = 0; i < m3.rows; i++) {
    m3.r[i] = vec_add(m1.r[i], m2.r[i]);
  }
  return m3;
}

void mat_add_i(matrix_t * m1, matrix_t m2) {
  if (_DEBUG_) {
    check_fail(m1->cols == m2.cols && m1->rows == m2.rows, "mat_add_i",
                          "matrices must have the same dimensions");
  }
  int i;
  for (i = 0; i < m1->rows; i++) {
    vec_add_i(&m1->r[i], m2.r[i]);
  }
}

void mat_dispose(matrix_t * m) {
  if (_DEBUG_) {
    check_fail(m == NULL, "mat_dispose", "matrix is NULL");
    check_fail(m->r == NULL, "mat_dispose", "matrix rows NULL");
  }
  int i;
  for (i = 0; i < m->rows; i++) {
    vec_dispose(&m->r[i]);
  }
  free(m->r);
  m->r = NULL;
  m->rows = -1;
  m->cols = -1;
}

vector_t mat_dotvr(matrix_t m, vector_t v) {
  if (_DEBUG_) check_fail(m.cols != v.dim, "mat_dotvr",
                          "matrix and vector have incompatible shapes");
  vector_t mdot = vec_init(m.rows);
  int i;
  for (i = 0; i < m.rows; i++) {
    mdot.comp[i] = vec_dot(m.r[i], v);
  }
  return mdot;
}

matrix_t mat_init(int rows, int cols) {
  if (_DEBUG_) {
    check_fail(rows < 1, "mat_init", "invalid number of rows");
    check_fail(cols < 1, "mat_init", "invalid number of columns");
  }
  matrix_t m;
  m.r = malloc(sizeof(vector_t) * rows);
  int i;
  for (i = 0; i < rows; i++) {
    m.r[i] = vec_init(cols);
  }
  m.rows = rows;
  m.cols = cols;
  return m;
}

vector_t mat_mean(matrix_t m) {
  return vec_mul_s(1.0 / (double)m.rows, mat_sum(m));
}

matrix_t mat_new(int rows, int cols, ...) {
  va_list argp;
  va_start(argp, cols);
  matrix_t m = mat_init(rows, cols);
  int i;
  for (i = 0; i < rows; i++) {
    m.r[i] = va_arg(argp, vector_t);
  }
  va_end(argp);
  return m;
}

vector_t mat_principal_axis(matrix_t m) {
  matrix_t shift = mat_shift(m);
  vector_t dir = vec_new(m.cols);
  int i, n;
  /* axis is initialized to a random direction */
  for (i = 0; i < m.cols; i++) {
    dir.comp[i] = 2.0 * drand48() - 1.0;
  }
  vector_t mdot = mat_dotvr(shift, dir);
  for (n = 0; n < _PA_ITERATIONS_; n++) {
    for (i = 0; i < m.rows; i++) {
      vec_add_i(&dir, vec_mul_s(mdot.comp[i], shift.r[i]));
    }
  }
  vec_normalize_i(&dir);
  return dir;
}

void mat_print(matrix_t m) {
  printf("[ ");
  vec_print(m.r[0]);
  if (m.rows > 1) {
    int i;
    for (i = 1; i < m.rows - 1; i++) {
      printf("  ");
      vec_print(m.r[i]);
      printf(",\n");
    }
    printf("  ");
    vec_print(m.r[i]);
  }
  printf(" ]");
}

matrix_t mat_shift(matrix_t m) {
  vector_t mn = mat_mean(m);
  matrix_t sh = mat_init(m.rows, m.cols);
  int i;
  for (i = 0; i < m.rows; i++) {
    sh.r[i] = vec_sub(m.r[i], mn);
  }
  return sh;
}

vector_t mat_sum(matrix_t m) {
  vector_t sum = vec_zero(m.cols);
  int i;
  for (i = 0; i < m.rows; i++) {
    vec_add_i(&sum, m.r[i]);
  }
  return sum;
}

// TODO(rhennigan): finish mat_tostring def
char * mat_tostring(matrix_t m);

matrix_t mat_zero(int rows, int cols) {
  if (_DEBUG_) {
    check_fail(rows < 1, "mat_init", "invalid number of rows");
    check_fail(cols < 1, "mat_init", "invalid number of columns");
  }
  matrix_t m;
  m.r = malloc(sizeof(vector_t) * rows);
  int i;
  for (i = 0; i < rows; i++) {
    m.r[i] = vec_zero(cols);
  }
  m.rows = rows;
  m.cols = cols;
  return m;
}
