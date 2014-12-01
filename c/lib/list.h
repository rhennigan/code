// list.h - a simple implementation of singly-linked lists
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_LIST_H_
#define LIB_LIST_H_

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

typedef struct list_s {
  void * head;
  struct list_s * tail;
} list_t;

typedef struct lpair_s {
  list_t * left;
  list_t * right;
} lpair_t;

typedef int    (*cmp_f)(void * head1, void * head2);
typedef bool   (*sta_pred_f)(void * head);
typedef bool   (*dyn_pred_f)(void * head, void * dep_arg);
typedef void * (*fold_f)(void * head1, void * head2);

list_t * list_app(list_t * list, void * data);
list_t * list_copy(list_t * list);
void     list_dispose(list_t * list);
void     list_dump(list_t * list);
list_t * list_extremum(list_t * list, cmp_f ex);
list_t * list_filter(list_t * list, dyn_pred_f pred, void * dep_arg);
list_t * list_find(list_t * list, dyn_pred_f pred, void * dep_arg);
void *   list_foldl(list_t * list, void * acc, fold_f fold_fun);
void *   list_foldr(list_t * list, void * acc, void * (*f)(void * x, void * y));
list_t * list_fromarray(void * array, size_t objsize, size_t length);
void   * list_head(list_t * list);
void     list_iter(list_t * list, void (*f)(void * data));
list_t * list_join(list_t * list1, list_t * list2);
size_t   list_length(list_t * list);
list_t * list_map(list_t * list, void * (*f)(void * x));
lpair_t  list_partition(list_t * lst, cmp_fun pred, void * cmp_arg);
list_t * list_pre(list_t * list, void * data);
list_t * list_reverse(list_t * list);
list_t * list_sort(list_t * list, cmp_fun lt);
list_t * list_tail(list_t * list);
void   * list_toarray(list_t * list, size_t size);

#endif  // LIB_LIST_H_
