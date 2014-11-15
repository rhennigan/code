// bst.h - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_BINTREE_H_
#define LIB_BINTREE_H_

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>
#include <stdint.h>
#include "./list.h"

typedef enum { PRE_ORDER, IN_ORDER, POST_ORDER } order_t;

typedef struct bst_s {
  struct bst_s * left;
  struct bst_s * parent;
  struct bst_s * right;
  void *         data;
  size_t         depth;
} bst_t;

typedef int32_t (*cmp_f)(void * a, void * b);

size_t  bst_depth(bst_t * bst);
void    bst_dispose(bst_t * bst);
void    bst_dump(bst_t * bst, order_t order);
void    bst_flatten(bst_t * bst, list_t ** list, order_t order);
bst_t * bst_init();
bst_t * bst_insert(bst_t * bst, void * data, cmp_f cmp);
void    bst_print(bst_t * bst, void (*pr)(void * data));
void    bst_remove(bst_t * bst, void * data, cmp_f cmp);
void *  bst_search(bst_t * bst, void * data, void * result, cmp_f cmp);

#endif  // LIB_BINTREE_H_
