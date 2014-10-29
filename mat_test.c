// mat_test.c - testing matrix stuff
// Copyright (C) 2014 Richard Hennigan

#include <stdio.h>
#include <stdbool.h>
#include <time.h>
#include "math/vectors.h"
#include "math/matrices.h"

int main(/* int argc, char *argv[] */) {
  srand48((unsigned) time(NULL));
  printf("\n");

  matrix_t matrix = mat_rand(10, 4, 0.0, 150.0);
  printf("matrix:\n");
  mat_print(matrix, 0);
  printf("\n\n");

  vector_t mean = mat_mean(matrix);
  printf("mean:\n ");
  vec_print(mean);
  printf("\n\n");

  
  return 0;
}
