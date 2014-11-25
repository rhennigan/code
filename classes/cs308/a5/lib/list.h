// list.h - a simple implementation of doubly-linked lists
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_LIST_H_
#define LIB_LIST_H_

#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <stdio.h>

typedef struct list_s {
  struct list_s * prev;
  void *          head;
  struct list_s * next;
} list_t;

typedef struct lpart_s {
  list_t * psat;
  list_t * comp;
} lpart_t;

typedef bool (*cmp_fun)(void * a, void * b);

list_t * list_app(list_t * list, void * data);
list_t * list_copy(list_t * list);
void     list_dispose(list_t * list);
void     list_dump(list_t * list);
void *   list_find(list_t * list, void * h, cmp_fun eq);
list_t * list_fromarray(void * array, size_t objsize, size_t length);
void *   list_head(list_t * list);
void     list_iter(list_t * list, void (*f)(void * data));
list_t * list_join(list_t * list1, list_t * list2);
size_t   list_length(list_t * list);
list_t * list_map(list_t * list, void * (*f)(void * x));
void     list_partition(list_t * lst, cmp_fun pred, list_t ** d1, list_t ** d2);
list_t * list_pre(list_t * list, void * data);
list_t * list_reverse(list_t * list);
list_t * list_sort(list_t * list, cmp_fun lt);
list_t * list_tail(list_t * list);
void *   list_toarray(list_t * list, size_t size);

#endif  // LIB_LIST_H_
