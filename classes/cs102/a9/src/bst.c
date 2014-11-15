// bst.c - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bst.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))

static inline void check_null(void * addr, const char * msg) {
  if (addr == NULL) {
    printf("%s\n", msg);
    exit(EXIT_FAILURE);
  }
}

static inline bst_t * get_left(bst_t * bst) {
  check_null(bst, "get_left");
  return bst->left;
}

static inline bst_t * get_parent(bst_t * bst) {
  check_null(bst, "get_parent");
  return bst->parent;
}

static inline bst_t * get_right(bst_t * bst) {
  check_null(bst, "get_right");
  return bst->right;
}

static inline void * get_data(bst_t * bst) {
  check_null(bst, "get_data");
  return bst->data;
}

size_t  bst_depth(bst_t * bst);

void    bst_dispose(bst_t * bst);

void    bst_flatten(bst_t * bst, list_t ** list);

bst_t * bst_init() {
  bst_t * bst = malloc(sizeof(bst_t));
  assert(bst != NULL);
  bst->left   = NULL;
  bst->parent = NULL;
  bst->right  = NULL;
  bst->data   = NULL;
  bst->depth  = 0;
  return bst;
}

bst_t * bst_insert(bst_t * bst, void * data, cmp_f cmp);

void    bst_print(bst_t * bst);

void    bst_remove(bst_t * bst, void * data, cmp_f cmp);

void *  bst_search(bst_t * bst, void * data, void * result, cmp_f cmp);
