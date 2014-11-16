// main.c - testing bst.h and bst.c
// Copyright (C) 2014 Richard Hennigan

#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "lib/bst.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MIN(a, b) ((a) < (b) ? (a) : (b))

int32_t cmp(void * a, void * b) {
  char * x = (char*)a;
  char * y = (char*)b;
  return strcmp(x, y);
}

void pf(bst_t * bst) {
  if (bst == NULL || bst->data == NULL) return;
  printf(" %s", (char*)bst->data);
}

void ps(void * s) {
  printf("%s\n", (char*)s);
}

int main(int argc, char *argv[]) {
  bst_t * bst = bst_init();
  srand(time(NULL));
  for (int i = 0; i < argc - 1; i++) {
    printf("Inserting \"%s\"...\n", argv[i]);
    bst_insert(bst, argv[i], &cmp);
    bst_print(bst, NULL, &pf);
    printf("\n\n");
  }

  bst_update_depth(bst);

  printf("---------------------------------------------\n");
  printf("TREE COMPLETE, NOW BALANCING...\n");

  for (size_t i = 0; i < bst_height(bst)-1; i++) {
    printf("---------------------------------------------\n\n");
    bst = bst_balance(bst);
    bst_print(bst, NULL, &pf);
  }

  printf("---------------------------------------------\n");
  printf("TREE BALANCED, DISPLAYING IN-ORDER ITEMS\n");
  printf("---------------------------------------------\n");

  list_t * flat = NULL;
  bst_flatten(bst, &flat, IN_ORDER);
  list_iter(list_reverse(flat), &ps);

  for (int32_t i = 0; i < argc; i++) {
    
  }
  char * hello = "hello";
  bool found_hello = bst_search(bst, hello, cmp);
  printf("found hello: %s\n", found_hello ? "true" : "false");

  char * goodbye = "goodbyeo";
  bool found_goodbye = bst_search(bst, goodbye, cmp);
  printf("found goodbye: %s\n", found_goodbye ? "true" : "false");

  return 0;
}
