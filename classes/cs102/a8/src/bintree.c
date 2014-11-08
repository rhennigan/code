// bintree.c - binary tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bintree.h"

size_t bt_depth(bintree_t * tree);

void bt_dispose(bintree_t * tree);

bool bt_has_left(bintree_t * tree);

bool bt_has_right(bintree_t * tree);

bintree_t * bt_init();

void bt_insl(bintree_t * tree, void * data);

void bt_insr(bintree_t * tree, void * data);

bool bt_is_leaf(bintree_t * tree);

bool bt_is_node(bintree_t * tree);

size_t bt_leaf_count(bintree_t * tree);

size_t bt_node_count(bintree_t * tree);
