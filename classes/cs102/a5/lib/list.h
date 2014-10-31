#ifndef _LIB_LIST_H_
#define _LIB_LIST_H_

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
void list_insert(list_t * list, void * data);
void list_append(list_t * list, void * data);
void list_delete(list_t * list);
void list_dispose(list_t * list);

#endif
