// lib/list.h - Copyright 2014, Richard Hennigan

#ifndef LIB_LIST_H_
#define LIB_LIST_H_

typedef struct node_s {
  struct node_s * next;
  struct node_s * prev;
  void * data;
} node_t;

typedef struct list_s {
  node_t * head;
  node_t * tail;
  int length;
} list_t;

node_t * node_init(void * data);
list_t * list_init(void);
void list_insf(list_t * list, void * data);
void list_insr(list_t * list, void * data);
void list_delf(list_t * list);
void list_delr(list_t * list);
void list_dispose(list_t * list);

#endif  // LIB_LIST_H_
