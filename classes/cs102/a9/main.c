// main.c - testing bst.h and bst.c
// Copyright (C) 2014 Richard Hennigan

#include "lib/bst.h"

#define ARRSIZ 15

int32_t intcmp(void * a, void * b) {
  return *(int32_t*)a - *(int32_t*)b;
}

const uint32_t seed = 0;

int main(int argc, char *argv[]) {
  bst_t * bst = bst_init();
  int32_t arr[ARRSIZ];
  for (int32_t i = 0; i < ARRSIZ; i++) arr[i] = rand_r();
  return 0;
}
