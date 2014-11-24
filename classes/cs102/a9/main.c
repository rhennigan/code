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
  printf("  %s\n", (char*)s);
}

void search_test(bst_t * bst, char * str) {
  printf("  Searching for \"%s\"... ", str);
  bool found = bst_search(bst, str, cmp);
  printf("%s\n", found ? "FOUND" : "NOT FOUND");
}

void remove_test(bst_t * bst, char * remove) {
  printf("  Removing \"%s\"... \n\n", remove);
  bst_remove(bst, remove, cmp);
  bst_print(bst, NULL, &pf);
}

int main(int argc, char *argv[]) {
  bst_t * bst = bst_init();
  srand(time(NULL));

  printf("\n\n---------------------------------------------\n");
  printf("BUILDING TREE\n");
  printf("---------------------------------------------\n");

  for (int i = 0; i < argc; i++) {
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

  printf("\n\n---------------------------------------------\n");
  printf("TREE BALANCED, DISPLAYING IN-ORDER ITEMS\n");
  printf("---------------------------------------------\n");

  list_t * flat = NULL;
  bst_flatten(bst, &flat, IN_ORDER);
  list_iter(list_reverse(flat), &ps);

  printf("\n\n---------------------------------------------\n");
  printf("TESTING SEARCH\n");
  printf("---------------------------------------------\n");

  for (int32_t i = 0; i < argc; i++) {
    search_test(bst, argv[i]);
  }

  search_test(bst, "not present");
  search_test(bst, "missing");

  printf("\n\n---------------------------------------------\n");
  printf("TESTING REMOVAL\n");
  printf("---------------------------------------------\n\n");
  bst_print(bst, NULL, &pf);
  printf("\n");

  remove_test(bst, "strings");
  remove_test(bst, "./main");
  remove_test(bst, "binary");

  return 0;
}
