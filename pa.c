// Copyright 2014, Richard Hennigan

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include <assert.h>
#include <math.h>

typedef struct vector_s {
  int dim;
  double * v;
} vector_t;

vector_t vec_new(int dim) {
  vector_t a;
  a.v = malloc(sizeof(double) * dim);
  a.dim = dim;
  int i;
  for (i = 0; i < dim; i++) {
    a.v[i] = 0.0;
  }
  return a;
}

double vec_norm(vector_t a) {
  double n;
  int i;
  for (i = 0; i < a.dim; i++) {
    n += a.v[i] * a.v[i];
  }
  return sqrt(n);
}

vector_t vec_add(vector_t a, vector_t b) {
  assert(a.dim == b.dim);
  vector_t c = vec_new(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    c.v[i] = a.v[i] + b.v[i];
  }
  return c;
}

vector_t vec_sub(vector_t a, vector_t b) {
  assert(a.dim == b.dim);
  vector_t c = vec_new(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    c.v[i] = a.v[i] - b.v[i];
  }
  return c;
}

vector_t vec_s_mult(double c, vector_t a) {
  vector_t b = vec_new(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    b.v[i] = c * a.v[i];
  }
  return b;
}

vector_t vec_c_mult(vector_t a, vector_t b) {
  assert(a.dim == b.dim);
  vector_t c = vec_new(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    c.v[i] = a.v[i] * b.v[i];
  }
  return c;
}

vector_t vec_s_div(double d, vector_t a) {
  vector_t b = vec_new(a.dim);
  int i;
  for (i = 0; i < a.dim; i++) {
    b.v[i] = a.v[i] / d;
  }
  return b;
}

double vec_dist(vector_t a, vector_t b) {
  return vec_norm(vec_sub(a, b));
}

vector_t vec_normalized(vector_t a) {
  return vec_s_div(vec_norm(a), a);
}

double vec_dot(vector_t a, vector_t b) {
  assert(a.dim == b.dim);
  double dot;
  int i;
  for (i = 0; i < a.dim; i++) {
    dot += a.v[i] * b.v[i];
  }
  return dot;
}

typedef struct matrix_s {
  int cols;
  int rows;
  vector_t * m;
} matrix_t;

matrix_t matrix_new(int rows, int cols) {
  vector_t * mdata = malloc(sizeof(vector_t) * rows);
  matrix_t matrix;
  matrix.cols = cols;
  matrix.rows = rows;
  matrix.m = mdata;
  int i, j;
  for (i = 0; i < rows; i++) {
    matrix.m[i] = vec_new(cols);
    for (j = 0; j < cols; j++) {
      matrix.m[i].v[j] = 0.0;
    }
  }
  return matrix;
}

vector_t matrix_sum(matrix_t mat) {
  vector_t sum = vec_new(mat.cols);
  int i;
  for (i = 0; i < mat.rows; i++) {
    sum = vec_add(sum, mat.m[i]);
  }
  return sum;
}

vector_t matrix_mean(matrix_t mat) {
  vector_t mean = vec_s_div(mat.rows, matrix_sum(mat));
  return mean;
}

matrix_t matrix_shift(matrix_t mat) {
  vector_t mean = matrix_mean(mat);
  matrix_t shift = matrix_new(mat.rows, mat.cols);
  int i;
  for (i = 0; i < mat.rows; i++) {
    shift.m[i] = vec_sub(mat.m[i], mean);
  }
  return shift;
}

vector_t matrix_dotvr(matrix_t mat, vector_t v) {
  assert(mat.cols == v.dim);
  vector_t mdot = vec_new(mat.rows);
  int i;
  for (i = 0; i < mat.rows; i++) {
    mdot.v[i] = vec_dot(mat.m[i], v);
  }
  return mdot;
}

vector_t principal_axis(matrix_t mat) {
  matrix_t shift = matrix_shift(mat);
  vector_t dir = vec_new(mat.cols);
  int i, n;
  for (i = 0; i < dir.dim; i++) {
    dir.v[i] = 2.0 * drand48() - 1.0;
  }
  dir.v[0] = 1.0;
  vector_t mdot = matrix_dotvr(shift, dir);
  for (n = 0; n < 5; n++) {
    for (i = 0; i < mat.rows; i++) {
      dir = vec_add(dir, vec_s_mult(mdot.v[i], shift.m[i]));
    }
    dir = vec_normalized(dir);
  }
  return dir;
}

int main(int argc, char *argv[]) {
  int cols = 3;
  int rows = 100000;
  matrix_t matrix = matrix_new(rows, cols);
  srand48((unsigned) time(NULL));
  int i, j;
  for (i = 0; i < rows; i++) {
    matrix.m[i] = vec_new(cols);
    for (j = 0; j < cols; j++) {
      matrix.m[i].v[j] = (j * j * j + 1) * drand48();
    }
  }

  vector_t mean = matrix_mean(matrix);
  for (i = 0; i < mean.dim; i++) {
    printf("%f ", mean.v[i]);
  }
  printf("\n\n");

  vector_t paxis = principal_axis(matrix);
  for (i = 0; i < paxis.dim; i++) {
    printf("%f ", paxis.v[i]);
  }
  printf("\n\n");

  printf("norm = %f", vec_norm(paxis));


  return 0;
}


