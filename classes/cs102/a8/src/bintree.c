// bintree.c - binary tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bintree.h"

size_t bt_depth(bintree_t * bt);

void bt_dispose(bintree_t * bt);

bool bt_has_left(bintree_t * bt);

bool bt_has_right(bintree_t * bt);

bintree_t * bt_init() {
  bintree_t * bt = malloc(sizeof(bintree_t));
  assert(bt != NULL);
  bt->data  = NULL;
  bt->left  = NULL;
  bt->right = NULL;
  return bt;
}

void bt_insl(bintree_t * bt, void * data);

void bt_insr(bintree_t * bt, void * data);

bool bt_is_empty(bintree_t * bt) {
  assert(bt != NULL);
  return bt->data == NULL && bt->left == NULL && bt->right == NULL;
}

bool bt_is_leaf(bintree_t * bt) {
  if (bt_is_empty(bt)) return false;
}

bool bt_is_node(bintree_t * bt);

size_t bt_leaf_count(bintree_t * bt);

size_t bt_node_count(bintree_t * bt);
