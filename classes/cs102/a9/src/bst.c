// bst.c - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bst.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))

size_t  bst_depth(bst_t * bst);

void    bst_dispose(bst_t * bst);

void    bst_flatten(bst_t * bst, list_t ** list);

bst_t * bst_init();

bst_t * bst_insert(bst_t * bst, void * data, cmp_f cmp);

void    bst_print(bst_t * bst);

void    bst_remove(bst_t * bst, void * data, cmp_f cmp);

void *  bst_search(bst_t * bst, void * data, void * result, cmp_f cmp);

