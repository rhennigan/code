// list.h - basic cons list
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_LIST_H_
#define LIB_LIST_H_

#include <stdbool.h>
#include <stdlib.h>

typedef struct list_s {
  void * head;
  struct list_s * tail;
} list_t;

list_t * list_cons(list_t * list, void * head);
void     list_dispose(list_t * list);
void     list_dump(list_t * list);
void *   list_find(list_t * list, void * h, bool (*cmp)(void * a, void * b));
void *   list_head(list_t * list);
list_t * list_init();
void     list_iter(list_t * list, void (*f)(void * head));
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
