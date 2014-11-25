// list.h - a simple implementation of singly-linked lists
// Copyright (C) 2014 Richard Hennigan

#include "../lib/list.h"

/******************************************************************************/
/* PRIVATE FUNCTIONS                                                          */
/******************************************************************************/

static inline list_t * last_node(list_t * list) {
  assert(list != NULL);
  while (list->tail != NULL) {
    list = list_tail(list);
  }  // end while (list->tail != NULL)
  return list;
}  // end last_node

static inline list_t * list_init() {
  list_t * list = malloc(sizeof(list_t));
  assert(list != NULL);
  list->head = NULL;
  list->tail = NULL;
  return list;
}  // end list_init

static inline list_t * list_cons(list_t * list, void * data) {
  list_t * new_list = list_init();
  new_list->head = data;
  new_list->tail = list;
  return new_list;
}  // end list_cons

static inline list_t * list_snoc(list_t * list, void * data) {
  list_t *last = list_init();
  last->head = data;
  if (list == NULL) {
    return last;
  } else {  // (list != NULL)
    last_node(list)->tail = last;
    return list;
  }  // end if (list == NULL)
}  // end list_snoc

/******************************************************************************/
/* PUBLIC FUNCTIONS                                                           */
/******************************************************************************/

void list_app(list_t ** list, void * data) {
  *list = list_snoc(*list, data);
}  // end list_app

list_t * list_copy(list_t * list) {
  list_t * new_list = NULL;
  list_t * tmp = list_init();
  while (list != NULL) {
    
  }
  return new_list;
}

void list_dispose(list_t * list) {
  if (list == NULL) return;
  list_t ** next = &list->tail;
  free(list);
  list = NULL;
  list_dispose(*next);
}  // end list_dispose

void list_dump(list_t * list) {
  printf("\nlist_dump: %p\n", list);
  printf("-------------------\n");
  printf(" list size: %lu\n", list_length(list));
  printf(" list contents:\n");
  if (list == NULL) {
    printf("  (nil)\n");
  } else {  // (list != NULL)
    while (list != NULL) {
      printf("  %p, %p\n", list_head(list), list_tail(list));
      list = list_tail(list);
    }  // end while (list != NULL)
  }  // end if (list == NULL)
}  // end list_dump

void * list_find(list_t * list, void * h, cmp_fun eq) {
  if (list == NULL) {
    return NULL;
  } else if ((*eq)(h, list_head(list))) {
    return list_head(list);
  } else {  // (list != NULL && !(*cmp)(h, list_head(list)))
    return list_find(list_tail(list), h, (*eq));
  }   // end if (list == NULL)
}  // end list_find

list_t * list_fromarray(void * array, size_t objsize, size_t length);

inline void * list_head(list_t * list) {
  if (list == NULL) {
    printf("list_head: list is empty\n");
    exit(EXIT_FAILURE);
  } else {  // (list != NULL)
    return list->head;
  }  // end if (list == NULL)
}  // end list_head

void list_iter(list_t * list, void (*f)(void * head)) {
  list_t * tmp = list;
  while (tmp != NULL) {
    (*f)(tmp->head);
    tmp = list_tail(tmp);
  }  // end while (tmp != NULL)
}  // end list_iter

list_t * list_join(list_t * list1, list_t * list2);

size_t list_length(list_t * list) {
  size_t len = 0;
  while (list != NULL) {
    len++;
    list = list_tail(list);
  }  // end while (list != NULL)
  return len;
}  // end list_length

list_t * list_map(list_t * list, void * (*f)(void * x)) {
  if (list == NULL) {
    return NULL;
  } else {  // (list != NULL)
    return list_cons(list_map(list_tail(list), f), f(list_head(list)));
  }  // end if (list == NULL)
}

void list_pre(list_t ** list, void * data) {
  *list = list_cons(*list, data);
}  // end list_app

list_t * list_reverse(list_t * list) {
  list_t * new_list = NULL;
  while (list != NULL) {
    new_list = list_cons(new_list, list_head(list));
    list = list_tail(list);
  }  // end while (list != NULL)
  return new_list;
}  // end list_reverse

inline list_t * list_tail(list_t * list) {
  if (list == NULL) {
    printf("list_tail: list is empty\n");
    exit(EXIT_FAILURE);
  } else {  // (list != NULL)
    return list->tail;
  }  // end if (list == NULL)
}  // end list_tail

void * list_toarray(list_t * list, size_t size);
