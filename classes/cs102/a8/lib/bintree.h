// bintree.h - binary tree
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_BINTREE_H_
#define LIB_BINTREE_H_

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

typedef struct bintree_s {
  struct bintree_s * left;
  void * data;
  struct bintree_s * right;
} bintree_t;

size_t      bt_depth(bintree_t * tree);
void        bt_dispose(bintree_t * tree);
bool        bt_has_left(bintree_t * tree);
bool        bt_has_right(bintree_t * tree);
bintree_t * bt_init();
void        bt_insl(bintree_t * tree, void * data);
void        bt_insr(bintree_t * tree, void * data);
bool        bt_is_empty(bintree_t * tree);
bool        bt_is_leaf(bintree_t * tree);
bool        bt_is_node(bintree_t * tree);
size_t      bt_leaf_count(bintree_t * tree);
size_t      bt_node_count(bintree_t * tree);

#endif  // LIB_BINTREE_H_
