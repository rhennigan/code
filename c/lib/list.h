// list.h - a simple implementation of singly-linked lists
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_LIST_H_
#define LIB_LIST_H_

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

extern long int counter;

typedef void * data_t;

typedef struct list_s {
  data_t head;
  struct list_s * tail;
} list_t;

typedef struct lpair_s {
  list_t * left;
  list_t * right;
} lpair_t;

typedef bool   (*sta_cmp_f)(void * head1, void * head2);
typedef bool   (*dyn_cmp_f)(data_t head1, data_t head2, void * dep_arg);
typedef bool   (*sta_pred_f)(data_t head);
typedef bool   (*dyn_pred_f)(data_t head, void * dep_arg);
typedef void * (*fold_f)(void * acc, data_t head);
typedef void   (*iter_f)(data_t data);
typedef data_t (*map_f)(data_t data);

list_t * list_app(list_t * list, data_t data);
list_t * list_copy(list_t * list);
void     list_dispose(list_t * list);
void     list_dump(list_t * list);
list_t * list_extremum(list_t * list, dyn_cmp_f ex, void * dep_arg);
list_t * list_filter(list_t * list, dyn_pred_f pred, void * dep_arg);
list_t * list_find(list_t * list, dyn_pred_f pred, void * dep_arg);
void   * list_fold(list_t * list, void * acc, fold_f f);
void   * list_foldl(list_t * list, void * acc, fold_f f);
void   * list_foldr(list_t * list, void * acc, fold_f f);
list_t * list_fromarray(void * array, size_t objsize, size_t length);
void   * list_head(list_t * list);
void     list_iter(list_t * list, iter_f f);
list_t * list_join(list_t * list1, list_t * list2);
size_t   list_length(list_t * list);
list_t * list_map(list_t * list, map_f f);
lpair_t  list_partition(list_t * lst, dyn_pred_f pred, void * dep_arg);
list_t * list_pre(list_t * list, data_t data);
list_t * list_reverse(list_t * list);
list_t * list_skip(list_t * list, size_t n);
list_t * list_sort(list_t * list, sta_cmp_f cmp);
list_t * list_tail(list_t * list);
data_t * list_toarray(list_t * list, size_t obj_size);

#endif  // LIB_LIST_H_
