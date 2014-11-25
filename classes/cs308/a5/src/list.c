// list.h - a simple implementation of singly-linked lists
// Copyright (C) 2014 Richard Hennigan

#include "../lib/list.h"

/******************************************************************************/
/* PRIVATE FUNCTIONS                                                          */
/******************************************************************************/

static inline list_t * last_node(list_t * list) {
  assert(list != NULL);
  while (list->next != NULL) {
    list = list_tail(list);
  }  // end while (list->next != NULL)
  return list;
}  // end last_node

static inline list_t * list_init() {
  list_t * list = malloc(sizeof(list_t));
  assert(list != NULL);
  list->head = NULL;
  list->next = NULL;
  return list;
}  // end list_init

static inline list_t * list_cons(list_t * list, void * data) {
  list_t * new_list = list_init();
  new_list->head = data;
  new_list->next = list;
  return new_list;
}  // end list_cons

static inline list_t * list_snoc(list_t * list, void * data) {
  list_t *last = list_init();
  last->head = data;
  if (list == NULL) {
    return last;
  } else {  // (list != NULL)
    last_node(list)->next = last;
    return list;
  }  // end if (list == NULL)
}  // end list_snoc

/******************************************************************************/
/* PUBLIC FUNCTIONS                                                           */
/******************************************************************************/

list_t * list_app(list_t * list, void * data) {
  list_t * new_list = list_copy(list);
  list_t * last = last_node(new_list);
  last->next = list_init();
  last->next->head = data;
  return new_list;
}  // end list_app

list_t * list_copy(list_t * list) {
  if (list == NULL) {
    return NULL;
  } else {  // (list != NULL)
    return list_cons(list_copy(list_tail(list)), list_head(list));
  }  // end if (list == NULL)
}  // end list_copy

void list_dispose(list_t * list) {
  if (list == NULL) return;
  list_t ** next = &list->next;
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
      printf("  %p (%p)\n", list, list_head(list));
      list = list_tail(list);
    }  // end while (list != NULL)
    printf("  %p\n", list);
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

list_t * list_fromarray(void * array, size_t objsize, size_t length) {
  list_t * list = NULL;
  for (int i = (length-1) * objsize; i >= 0; i -= objsize) {
    list = list_cons(list, array+i);
  }  // end for (int i = (length-1) * objsize; i >= 0; i -= objsize)
  return list;
}  // end list_fromarray

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

list_t * list_join(list_t * list1, list_t * list2) {
  list_t * list = list_copy(list1);
  last_node(list)->next = list2;
  return list;
}  // end list_join

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

lpair_t list_partition(list_t * list, cmp_fun pred, void * pivot) {
  lpair_t pair = { NULL, NULL };
  while (list != NULL) {
    void * x = list_head(list);
    if (pred(x, pivot)) {
      pair.left = list_cons(pair.left, x);
    } else {  // (!pred(x, pivot))
      pair.right = list_cons(pair.right, x);
    }  // end if (pred(x, pivot))
    list = list_tail(list);
  }  // end while (list != NULL)
  return pair;
}

list_t * list_pre(list_t * list, void * data) {
  return list_cons(list, data);
}  // end list_app

list_t * list_reverse(list_t * list) {
  list_t * new_list = NULL;
  while (list != NULL) {
    new_list = list_cons(new_list, list_head(list));
    list = list_tail(list);
  }  // end while (list != NULL)
  return new_list;
}  // end list_reverse

static inline list_t * merge(list_t * xxs, list_t * yys, cmp_fun lt) {
  if (xxs == NULL && yys == NULL) {
    return NULL;
  } else if (xxs == NULL) {
    return yys;
  } else if (yys == NULL) {
    return xxs;
  } else {  // (xs != NULL && ys != NULL)
    void * x = list_head(xxs);
    void * y = list_head(yys);
    list_t * xs = list_tail(xxs);
    list_t * ys = list_tail(yys);
    list_t * merged = merge(xs, ys, lt);
    if (lt(x, y)) {
      return list_cons(list_cons(merged, y), x);
    } else {  // (!lt(x, y))
      return list_cons(list_cons(merged, x), y);
    }  // end if (lt(x, y))
  }  // end if (xs == NULL && ys == NULL)
}

list_t * list_sort(list_t * list, cmp_fun lt) {
  printf("\n\nsorting list: \n");
  list_dump(list);
  fflush(NULL);
  if (list == NULL) {
    return NULL;
  } else {  // (list != NULL)
    void * pivot = list_head(list);
    lpair_t part = list_partition(list, lt, pivot);
    part.left = list_sort(part.left, lt);
    part.right = list_sort(part.right, lt);
    return merge(part.left, part.right, lt);
  }  // end if (list == NULL)
}  // end list_sort

inline list_t * list_tail(list_t * list) {
  if (list == NULL) {
    printf("list_tail: list is empty\n");
    exit(EXIT_FAILURE);
  } else {  // (list != NULL)
    return list->next;
  }  // end if (list == NULL)
}  // end list_next

void * list_toarray(list_t * list, size_t size);
