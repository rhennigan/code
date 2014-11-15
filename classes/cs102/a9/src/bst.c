// bst.c - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bst.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))

/******************************************************************************/
/* PROTECTED MEMBER ACCESS FUNCTIONS                                          */
/******************************************************************************/

static inline void check_null(void * addr, const char * msg) {
  if (addr == NULL) {
    printf("%p: %s\n", addr, msg);
    exit(EXIT_FAILURE);
  }
}

static inline bst_t * left(bst_t * bst) {
  check_null(bst, "left");
  return bst->left;
}

static inline bst_t * parent(bst_t * bst) {
  check_null(bst, "parent");
  return bst->parent;
}

static inline bst_t * right(bst_t * bst) {
  check_null(bst, "right");
  return bst->right;
}

static inline void * data(bst_t * bst) {
  check_null(bst, "data");
  return bst->data;
}

static inline size_t depth(bst_t * bst) {
  check_null(bst, "depth");
  return bst->depth;
}

/******************************************************************************/
/* ADDITIONAL PRIVATE FUNCTIONS                                               */
/******************************************************************************/

static bst_t * rotate_right(bst_t * center) {
  bst_t *A, *B, *E;
  A = center;
  B = E = NULL;
  if (A) {
    B = A->left;
  }
  if (B) {
    E = B->right;
    B->right = A;
    B->parent = A->parent;
  }
}

static void balance(bst_t * bst) {
  bst_t * left_tree = left(bst);
  bst_t * right_tree = right(bst);
  return;
}

/******************************************************************************/
/* PUBLIC FUNCTIONS                                                           */
/******************************************************************************/

size_t bst_depth(bst_t * bst) {
  return depth(bst);
}

void    bst_dispose(bst_t * bst);

void    bst_flatten(bst_t * bst, list_t ** list);

bst_t * bst_init() {
  bst_t * bst = malloc(sizeof(bst_t));
  check_null(bst, "bst_init: malloc");
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
