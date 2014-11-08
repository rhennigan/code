// bintree.h - binary tree
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_BINTREE_H_
#define LIB_BINTREE_H_

#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include "./list.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))

typedef struct bintree_s {
  struct bintree_s * left;
  void * data;
  struct bintree_s * right;
} bintree_t;

size_t      bt_depth(bintree_t * bt);
void        bt_dispose(bintree_t * bt);
void        bt_flatten(bintree_t * bt, list_t * list);
bintree_t * bt_get_left(bintree_t * bt);
bintree_t * bt_get_right(bintree_t * bt);
bool        bt_has_data(bintree_t * bt);
bool        bt_has_left(bintree_t * bt);
bool        bt_has_right(bintree_t * bt);
bintree_t * bt_init();
void        bt_insl(bintree_t * bt, void * data);
void        bt_insr(bintree_t * bt, void * data);
bool        bt_is_empty(bintree_t * bt);
bool        bt_is_leaf(bintree_t * bt);
bool        bt_is_node(bintree_t * bt);
size_t      bt_leaf_count(bintree_t * bt);
size_t      bt_node_count(bintree_t * bt);

#endif  // LIB_BINTREE_H_
