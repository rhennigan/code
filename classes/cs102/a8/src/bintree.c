// bintree.c - binary tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bintree.h"

size_t bt_depth(bintree_t * bt) {
  if (bt == NULL) {
    return 0;
  } else if (bt_is_leaf(bt)) {
    return 1;
  } else {
    size_t ld = bt_depth(bt_get_left(bt));
    size_t rd = bt_depth(bt_get_right(bt));
    return 1 + MAX(ld, rd);
  }
}

void bt_dispose(bintree_t * bt) {
  if (bt == NULL) return;
  bintree_t ** l = &bt->left;
  bintree_t ** r = &bt->right;
  free(bt);
  bt = NULL;
  bt_dispose(*l);
  bt_dispose(*r);
}

void bt_flatten(bintree_t * bt, list_t * list) {
  if (bt_is_leaf(bt)) {
    list = list_cons(list, bt_get_data(bt));
  }
}

void * bt_get_data(bintree_t * bt) {
  assert(bt != NULL);
  return bt->data;
}

bintree_t * bt_get_left(bintree_t * bt) {
  assert(bt != NULL);
  return bt->left;
}

bintree_t * bt_get_right(bintree_t * bt) {
  assert(bt != NULL);
  return bt->right;
}

bool bt_has_data(bintree_t * bt) {
  assert(bt != NULL);
  return bt->data != NULL;
}

bool bt_has_left(bintree_t * bt) {
  assert(bt != NULL);
  return bt->left != NULL;
}

bool bt_has_right(bintree_t * bt) {
  assert(bt != NULL);
  return bt->right != NULL;
}

bintree_t * bt_init() {
  bintree_t * bt = malloc(sizeof(bintree_t));
  assert(bt != NULL);
  bt->data  = NULL;
  bt->left  = NULL;
  bt->right = NULL;
  return bt;
}

void bt_insl(bintree_t * bt, void * data) {
  assert(bt != NULL);
  assert(bt->left == NULL);
  bt->left = bt_init();
  bt->left->data = data;
}

void bt_insr(bintree_t * bt, void * data) {
  assert(bt != NULL);
  assert(bt->right == NULL);
  bt->right = bt_init();
  bt->right->data = data;
}

bool bt_is_empty(bintree_t * bt) {
  return !bt_has_data(bt) && !bt_has_left(bt) && !bt_has_right(bt);
}

bool bt_is_leaf(bintree_t * bt) {
  return bt_has_data(bt) && !bt_has_left(bt) && !bt_has_right(bt);
}

bool bt_is_node(bintree_t * bt) {
  return bt_has_left(bt) || bt_has_right(bt);
}

size_t bt_leaf_count(bintree_t * bt) {
  if (bt == NULL) {
    return 0;
  } else if (bt_is_leaf(bt)) {
    return 1;
  } else {
    size_t lc = bt_leaf_count(bt_get_left(bt));
    size_t rc = bt_leaf_count(bt_get_right(bt));
    return lc + rc;
  }
}

size_t bt_node_count(bintree_t * bt) {
  if (bt == NULL) {
    return 0;
  } else if (bt_is_node(bt)) {
    size_t lc = bt_node_count(bt_get_left(bt));
    size_t rc = bt_node_count(bt_get_right(bt));
    return lc + rc;
  } else {
    return 0;
  }
}
