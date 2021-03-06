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

typedef int32_t (*cmp_fun)(void * a, void * b);
typedef void (*pr_fun)(bst_t * bst);

typedef struct trunk_s {
  struct trunk_s * prev;
  char *           str;
} trunk_t;

typedef struct ins_arg_s {
  bst_t * bst;
  void * data;
  cmp_fun cmp;
} ins_arg_t;

bst_t *  bst_balance(bst_t * bst);
void     bst_dispose(bst_t * bst);
void     bst_dump(bst_t * bst, order_t order);
void     bst_flatten(bst_t * bst, list_t ** list, order_t order);
size_t   bst_height(bst_t * bst);
bst_t *  bst_init();
void     bst_insert(bst_t * bst, void * data, cmp_fun cmp);
size_t   bst_leaf_count(bst_t * bst);
size_t   bst_node_count(bst_t * bst);
void     bst_print(bst_t * bst, trunk_t * prev, pr_fun pf);
void     bst_remove(bst_t * bst, void * data, cmp_fun cmp);
bool     bst_search(bst_t * bst, void * data, cmp_fun cmp);
void     bst_update_depth(bst_t * bst);

bst_t * rotate_left(bst_t * bst);
bst_t * rotate_right(bst_t * bst);

#endif  // LIB_BINTREE_H_
