// list.c - basic cons list
// Copyright (C) 2014 Richard Hennigan

#include "../lib/list.h"

list_t * list_app(list_t * list, void * data) {
  list_t *last = list_init();
  last->head = data;
  if (list == NULL) {
    return last;
  } else {  // (list != NULL)
    list_t * tmp = list;
    do {
      if (tmp->tail == NULL) tmp->tail = last;
    } while ((tmp = list_tail(tmp)) != NULL);
    return list;
  }  // end if (list == NULL)
}  // end list_app

list_t * list_cons(list_t * list, void * head) {
  list_t * new_list = list_init();
  new_list->head = head;
  new_list->tail = list;
  return new_list;
}  // end list_cons

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

void * list_find(list_t * list, void * h, bool (*cmp)(void * a, void * b)) {
  if (list == NULL) {
    return NULL;
  } else if ((*cmp)(h, list_head(list))) {
    return list_head(list);
  } else {  // (list != NULL && !(*cmp)(h, list_head(list)))
    return list_find(list_tail(list), h, (*cmp));
  }   // end if (list == NULL)
}  // end list_find

inline void * list_head(list_t * list) {
  if (list == NULL) {
    printf("list_head: list is empty\n");
    exit(EXIT_FAILURE);
  } else {  // (list != NULL)
    return list->head;
  }  // end if (list == NULL)
}  // end list_head

inline list_t * list_init() {
  list_t * list = malloc(sizeof(list_t));
  assert(list != NULL);
  list->head = NULL;
  list->tail = NULL;
  return list;
}  // end list_init

void list_iter(list_t * list, void (*f)(void * head)) {
  list_t * tmp = list;
  while (tmp != NULL) {
    (*f)(tmp->head);
    tmp = list_tail(tmp);
  }  // end while (tmp != NULL)
}  // end list_iter

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
