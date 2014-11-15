// main.c - testing bst.h and bst.c
// Copyright (C) 2014 Richard Hennigan

#include <stdlib.h>
#include "lib/bst.h"

#define ARRSIZ 15

int32_t intcmp(void * a, void * b) {
  int32_t x = *(int32_t*)a;
  int32_t y = *(int32_t*)b;
  return x - y;
}

void print_node(bst_t * node) {
  size_t shift = 4 * bst_depth(node);
  for (size_t i = 0; i < shift; i++)  printf(" ");
  void * data = node->data;
  printf("d\n", *(int32_t*)get_data(node));
}

int main(int argc, char *argv[]) {
  bst_t * bst = bst_init();
  int64_t arr[ARRSIZ];
  for (int32_t i = 0; i < ARRSIZ; i++) {
    arr[i] = rand();
    printf("%lu\n", arr[i]);
    bst_insert(bst, &arr[i], &intcmp);
  }
  return 0;
}
