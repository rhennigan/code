// main.c - testing bst.h and bst.c
// Copyright (C) 2014 Richard Hennigan

#include <stdlib.h>
#include "lib/bst.h"

#define ARRSIZ 3

int32_t intcmp(void * a, void * b) {
  int32_t x = *(int32_t*)a;
  int32_t y = *(int32_t*)b;
  return x - y;
}

#define INDENTSZ 4
size_t offset = 0;

void print_node(bst_t * node) {
  if (node == NULL) return;
  if (node->data != NULL) {
    size_t shift = INDENTSZ * bst_depth(node);
    for (size_t i = 0; i < shift; i++)  printf(" ");
    int32_t * data = node->data;
    printf("%lu, %d\n", bst_depth(node), *data);
  }
}

int main(int argc, char *argv[]) {
  bst_t * bst = bst_init();
  int64_t arr[ARRSIZ];
  for (int32_t i = 0; i < ARRSIZ; i++) {
    arr[i] = rand();
    bst_insert(bst, &arr[i], &intcmp);
  }

  offset = force_depth(bst);
  bst_print(bst, &print_node);
  return 0;
}
