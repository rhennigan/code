// main.c - testing bst.h and bst.c
// Copyright (C) 2014 Richard Hennigan

#include "lib/bst.h"

int32_t intcmp(void * a, void * b) {
  return *(int32_t*)a - *(int32_t*)b;
}

int main(int argc, char *argv[]) {
  bst_t * bst = bst_init();
  return 0;
}
