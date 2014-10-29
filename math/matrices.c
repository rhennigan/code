// matrices.c - matrix stuff
// Copyright (C) 2014 Richard Hennigan

#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <string.h>
#include <stdbool.h>
#include "./vectors.h"
#include "./matrices.h"
#include "./utils.h"

#define _DEBUG_ true
#define _PA_ITERATIONS_ 5
#define _PPREC_ "3"
#define _SPREC_ "3"

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

#define _M_TL "\u250C"
#define _M_TR "\u2510"
#define _M_BL "\u2514"
#define _M_BR "\u2518"
#define _M_VT "\u2502"

void mat_print(matrix_t m, int indent) {
  int i, j;
  char * lsp = malloc(indent + 1);
  memset(lsp, ' ', indent);
  lsp[indent + 1] = '\0';
  int md = 1;
  bool sgn = false;
  for (i = 0; i < m.rows; i++) {
    for (j = 0; j < m.cols; j++) {
      double val = log10(fabs(m.r[i].comp[j])) + 1.0;
      md = (int)val > md ? (int)val : md;
      if (m.r[i].comp[j] < 0.0) sgn = true;
    }
  }
  int p = atoi(_PPREC_);
  int cw = m.cols * (md + p + (sgn ? 2 : 1)) + m.cols + 1;
  /* printf("m.cols = %d, md = %d, p = %d\n", m.cols, md, p); */
  /* printf("comp width = %d\n", (md + p + 2)); */
  char * fmt = malloc(BUFSIZ);
  snprintf(fmt, sizeof(fmt), "%%%d.%df ", md + p + (sgn ? 2 : 1), p);

  // print top of matrix
  printf("%s"_M_TL, lsp);
  for (j = 0; j < cw; j++) {
    printf(" ");
  }
  printf(_M_TR"\n");

  // print all rows
  for (i = 0; i < m.rows; i++) {
    printf("%s"_M_VT" ", lsp);  // left bracket
    // print all columns
    for (j = 0; j < m.cols; j++) {
      printf(fmt, m.r[i].comp[j]);
    }
    printf(_M_VT"\n");  // right bracket
  }

  // print bottom of matrix
  printf("%s"_M_BL, lsp);
  for (j = 0; j < cw; j++) {
    printf(" ");
  }
  printf(_M_BR"\n");
}

matrix_t mat_rand(int rows, int cols, double low, double high) {
  matrix_t rand = mat_init(rows, cols);
  int i;
  for (i = 0; i < rows; i++) {
    rand.r[i] = vec_rand(cols, low, high);
  }
  return rand;
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
