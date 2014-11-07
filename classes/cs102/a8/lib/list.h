// list.h - basic cons list
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_LIST_H_
#define LIB_LIST_H_

#include <stdbool.h>

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
list_t * list_tail(list_t * list);

#define list_cons_c(lst, i, t) do {             \
    t * n = malloc(sizeof(t));                  \
    *n = i;                                     \
    lst = list_cons(lst, n);                    \
  } while (0)

#endif  // LIB_LIST_H_
