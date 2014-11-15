// bst.h - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_BINTREE_H_
#define LIB_BINTREE_H_

#include <stdlib.h>
#include "./list.h"

typedef struct bst_s {
  struct bst_s * left;
  struct bst_s * parent;
  struct bst_s * right;
  void *         data;
  size_t         depth;
} bst_t;

size_t  bst_depth(bst_t * bst);
void    bst_dispose(bst_t * bst);
void    bst_flatten(bst_t * bst, list_t ** list);
bst_t * bst_init();
bst_t * bst_insert(bst_t * bst, void * data);
void    bst_print(bst_t * bst);

#endif  // LIB_BINTREE_H_
