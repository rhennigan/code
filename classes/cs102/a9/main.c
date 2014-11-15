// main.c - testing bst.h and bst.c
// Copyright (C) 2014 Richard Hennigan

#include <stdlib.h>
#include "lib/bst.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MIN(a, b) ((a) < (b) ? (a) : (b))

int32_t intcmp(void * a, void * b) {
  int32_t x = *(int32_t*)a;
  int32_t y = *(int32_t*)b;
  return x - y;
}

#define INDENTSZ 4
size_t offset = 0;

void print_node(bst_t * node) {
  if (node == NULL) {
    printf("\n");
    return;
  }
  if (node->data != NULL) {
    size_t shift = MAX(0, INDENTSZ * bst_depth(node) - 2);
    for (size_t i = 0; i < shift; i++)  printf(" ");
    int32_t * data = node->data;
    printf("--%d\n", *data);
  } else {
    printf("\n");
  }
}

int main(int argc, char *argv[]) {
  bst_t * bst = bst_init();
  size_t ARRSIZ = atoi(argv[1]);
  int64_t arr[ARRSIZ];
  for (size_t i = 0; i < ARRSIZ; i++) {
    arr[i] = rand() % 50 + 10;
    bst_insert(bst, &arr[i], &intcmp);
  }

  bst_update_depth(bst);
  bst_print(bst, &print_node);
  printf("---------------------------------------------\n");
  for (size_t i = 0; i < ARRSIZ; i++) {
    printf("%lu ", arr[i]);
  }

  return 0;
}
