// vec_test.c - testing vector stuff
// Copyright (C) 2014 Richard Hennigan

#include <stdio.h>
#include <stdbool.h>
#include "./vectors.h"

void print_status(vector_t a, const char * name) {
  printf("%s status:\n", name);
  char * vecstr = vec_tostring(a);
  printf(" vecstr = %s\n", vecstr);
  char * cstat = vec_cstat(a);
  printf(" cstat = %s\n", cstat);
  printf("\n");
}

int main(int argc, char *argv[]) {
  printf("\n");

  vector_t a = vec_new(3, 1.5, 2.0, -3.5);
  print_status(a, "a");

  vector_t b = vec_zero(3);
  print_status(b, "b");

  vector_t c = vec_add(a, b);
  print_status(c, "c");
  vec_add_i(&c, a);
  print_status(c, "c");

  vector_t d = vec_new(2, -1.2, 3.7);
  print_status(d, "d");

  vector_t e = vec_normalize(c);
  print_status(e, "e");
  return 0;
}
