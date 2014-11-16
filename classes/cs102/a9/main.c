// main.c - testing bst.h and bst.c
// Copyright (C) 2014 Richard Hennigan

#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "lib/bst.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MIN(a, b) ((a) < (b) ? (a) : (b))

/* int32_t intcmp(void * a, void * b) { */
/*   int32_t x = *(int32_t*)a; */
/*   int32_t y = *(int32_t*)b; */
/*   return x - y; */
/* } */

int32_t cmp(void * a, void * b) {
  char * x = (char*)a;
  char * y = (char*)b;
  return strcmp(x, y);
}

void pf(bst_t * bst) {
  if (bst == NULL || bst->data == NULL) return;
  printf(" %s", (char*)bst->data);
}

int main(int argc, char *argv[]) {
  bst_t * bst = bst_init();
  srand(time(NULL));
  for (int i = 0; i < argc - 1; i++) {
    bst_insert(bst, &argv[i], &cmp);
  }

  bst_update_depth(bst);

  printf("\n---------------------------------------------\n");
  bst_print(bst, NULL, &pf);

  printf("BALANCING\n");
  for (int i = 0; i < 3; i++) {
    printf("\n---------------------------------------------\n");
    bst = bst_balance(bst);
    printf("\n---------------------------------------------\n");
    bst_print(bst, NULL, &pf);
  }
  return 0;
}
