// bst.c - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bst.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))

/******************************************************************************/
/* PROTECTED MEMBER ACCESS FUNCTIONS                                          */
/******************************************************************************/

// Read functions

static inline void check_null(void * addr, const char * msg) {
  if (addr == NULL) {
    printf("%p: %s\n", addr, msg);
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

static inline size_t get_depth(bst_t * bst) {
  check_null(bst, "get_depth");
  return bst->depth;
}

// Write functions

static inline bst_t * set_left(bst_t * bst) {
  check_null(bst, "set_left");
  return bst->left;
}

static inline bst_t * set_parent(bst_t * bst) {
  check_null(bst, "set_parent");
  return bst->parent;
}

static inline bst_t * set_right(bst_t * bst) {
  check_null(bst, "set_right");
  return bst->right;
}

static inline void * set_data(bst_t * bst) {
  check_null(bst, "set_data");
  return bst->data;
}

static inline size_t set_depth(bst_t * bst) {
  check_null(bst, "set_depth");
  return bst->depth;
}

/******************************************************************************/
/* ADDITIONAL PRIVATE FUNCTIONS                                               */
/******************************************************************************/

static size_t force_depth(bst_t * bst) {
  if (bst == NULL) {
    return 0;
  } else if (is_leaf(bst)) {
    return 1;
  } else {
    size_t ld = force_depth(get_left(bst));
    size_t rd = force_depth(get_right(bst));
    size_t d = MAX(ld, rd);
    bst->depth = d;
    return d;
  }
}

static bst_t * rotate_right(bst_t * center) {
  bst_t *A, *B, *E;
  A = center;
  B = E = NULL;
  if (A) {
    B = A->get_left;
  }
  if (B) {
    E = B->get_right;
    B->get_right = A;
    B->get_parent = A->get_parent;
  }
}

static void balance(bst_t * bst) {
  bst_t * left_tree = get_left(bst);
  bst_t * right_tree = get_right(bst);
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
  bst->get_left   = NULL;
  bst->get_parent = NULL;
  bst->get_right  = NULL;
  bst->get_data   = NULL;
  bst->depth  = 0;
  return bst;
}

bst_t * bst_insert(bst_t * bst, void * get_data, cmp_f cmp);

void    bst_print(bst_t * bst);

void    bst_remove(bst_t * bst, void * get_data, cmp_f cmp);

void *  bst_search(bst_t * bst, void * get_data, void * result, cmp_f cmp);
