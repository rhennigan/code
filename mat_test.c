// mat_test.c - testing matrix stuff
// Copyright (C) 2014 Richard Hennigan

#include <stdio.h>
#include <stdbool.h>
#include <time.h>
#include <math.h>
#include "math/vectors.h"
#include "math/matrices.h"

int main(/* int argc, char *argv[] */) {
  srand48((unsigned) time(NULL));
  printf("\n");

  int rows = 1000000;
  int cols = 3;
  double low = -(double)rows / 10.0;
  double high = (double)rows / 10.0;
  matrix_t rmat = mat_rand(rows, cols, low, high);
  matrix_t matrix = mat_init(rows, cols);

  int i, j;
  for (i = 0; i < rows; i++) {
    for (j = 0; j < cols; j++) {
      matrix.r[i].c[j] = (double)(i *(j + 1)) + rmat.r[i].c[j];
    }
  }

  /* printf("matrix:\n"); */
  /* mat_print(matrix, 2); */

  clock_t start = clock(), diff;
  vector_t paxis = mat_principal_axis(matrix);
  diff = clock() - start;
  int msec = diff * 1000 / CLOCKS_PER_SEC;
  printf("principal axis (%d.%3d seconds):\n  ", msec / 1000, msec % 1000);
  vec_print(paxis);
  printf("\n\n");

  printf("principal axis (adjusted):\n  ");
  vec_print(vec_mul_s(paxis.c[0] < 0.0 ? -sqrt(14.0) : sqrt(14.0), paxis));
  printf("\n\n");
  
  return 0;
}
