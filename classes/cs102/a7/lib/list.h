// list.h - basic cons list
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_LIST_H_
#define LIB_LIST_H_

typedef struct list_s {
  void * head;
  struct list_s * tail;
} list_t;

list_t * list_cons(list_t * list, void * head);
void     list_dispose(list_t * list);
void *   list_head(list_t * list);
list_t * list_init();
void     list_iter(list_t * list, void (*f)(void * head));
list_t * list_tail(list_t * list);

#endif  // LIB_LIST_H_
