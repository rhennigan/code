// bst.h - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_BINTREE_H_
#define LIB_BINTREE_H_

#include <stdlib.h>
#include "./list.h"

typedef struct bst_n_s {
  struct bst_n_s * left;
  struct bst_n_s * parent;
  struct bst_n_s * right;
  void *         data;
  size_t         depth;
} bst_n_t;

typedef struct bst_s {
  bst_n_t * root;
} bst_t;

size_t  bst_depth(bst_n_t * bst);
void    bst_dispose(bst_n_t * bst);
void    bst_flatten(bst_n_t * bst, list_t ** list);
bst_n_t * bst_init();
bst_n_t * bst_initd(void * data);
bst_n_t * bst_insert(bst_n_t * bst, void * data);

#endif  // LIB_BINTREE_H_
