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

list_t * list_app(list_t * list, void * data);
list_t * list_cons(list_t * list, void * head);
void     list_dispose(list_t * list);
void     list_dump(list_t * list);
void *   list_find(list_t * list, void * h, bool (*cmp)(void * a, void * b));
list_t * list_fromarray(void * array, size_t objsize, size_t length);
void *   list_head(list_t * list);
void     list_iter(list_t * list, void (*f)(void * head));
list_t * list_join(list_t * list1, list_t * list2);
size_t   list_length(list_t * list);
list_t * list_map(list_t * list, void * (*f)(void * x));
list_t * list_reverse(list_t * list);
list_t * list_tail(list_t * list);
void *   list_toarray(list_t * list, size_t size);

#define list_cons_c(list, item, type) do {      \
    type * mem = malloc(sizeof(type));          \
    *mem = item;                                \
    list = list_cons(list, mem);                \
  } while (0)

#endif  // LIB_LIST_H_
