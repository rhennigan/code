// list.h - a simple implementation of singly-linked lists
// Copyright (C) 2014 Richard Hennigan

#include "../lib/list.h"

long int counter = 0;

/******************************************************************************/
/* PRIVATE FUNCTIONS                                                          */
/******************************************************************************/

static inline list_t * last_node(list_t * list) {
  if (list == NULL) {
    return NULL;
  } else {
    while (list->tail != NULL) {
      list = list->tail;
    }
    return list;
  }
}  // last_node

static inline list_t * list_init() {
  list_t * list = malloc(sizeof(list_t));
  if (list != NULL) {
    list->head = NULL;
    list->tail = NULL;
  }
  return list;
}  // list_init

static inline list_t * list_cons(list_t * list, data_t data) {
  list_t * new_list = list_init();
  new_list->head = data;
  new_list->tail = list;
  return new_list;
}  // list_cons

static inline list_t * list_snoc(list_t * list, data_t data) {
  list_t * last = list_init();
  last->head = data;
  if (list == NULL) {
    return last;
  } else {
    last_node(list)->tail = last;
    return list;
  }
}  // list_snoc

/******************************************************************************/
/* PUBLIC FUNCTIONS                                                           */
/******************************************************************************/
inline list_t * list_app(list_t * list, data_t head) {
  if (list == NULL) {
    list       = list_init();
    list->head = head;
  } else {
    list_t * last    = last_node(list);
    last->tail       = list_init();
    last->tail->head = head;
  }
  return list;
}  // list_app

inline list_t * list_copy(list_t * list) {
  if (list == NULL) {
    return NULL;
  } else {
    return list_cons(list_copy(list_tail(list)), list_head(list));
  }
}  // list_copy

inline void list_dispose(list_t * list) {
  list_t * tail;
  while (list != NULL) {
    tail = list_tail(list);
    free(list);
    list = tail;
  }
}  // list_dispose

inline void list_dump(list_t * list) {
  printf("\nlist_dump: %p\n", list);
  printf("-------------------\n");
  printf(" list size: %lu\n", list_length(list));
  printf(" list contents:\n");
  if (list == NULL) {
    printf("  (nil)\n");
  } else {
    while (list != NULL) {
      printf("  %p (%p)\n", list, list_head(list));
      list = list_tail(list);
    }
    printf("  %p\n", list);
  }
}  // list_dump

inline list_t * list_extremum(list_t * list, dyn_cmp_f ex, void * dep_arg) {
  if (list == NULL) {
    return NULL;
  } else {
    list_t * keep = list;
    list_t * next = list;
    while ((next = list_tail(next)) != NULL) {
      if (ex(list_head(next), list_head(keep), dep_arg))
        keep = next;
    }
    return keep;
  }
}  // list_extremum

inline list_t * list_filter(list_t * list, dyn_pred_f pred, void * dep_arg) {
  if (list == NULL) {
    return NULL;
  } else {
    list_t * filtered = list_init();
    list_t * tmp = filtered;
    while ((list = list_tail(list)) != NULL) {
      if (pred(list_head(list), dep_arg)) {
        tmp->head = list_head(list);
        tmp->tail = list_init();
        tmp       = list_tail(tmp);        
      }
    }
    if (list_head(filtered) == NULL) {
      free(filtered);
      return NULL;
    } else {
      return filtered;
    }
  }
}  // list_filter

inline void * list_fold(list_t * list, void * acc, fold_f f) {
  while (list != NULL) {
    acc  = f(acc, list_head(list));
    list = list_tail(list);
  }
  return acc;
}  // list_fold

inline void * list_foldl(list_t * list, void * acc, fold_f f) {
  if (list == NULL) {
    return acc;
  } else {
    data_t   x  = list_head(list);
    list_t * xs = list_tail(list);
    return list_foldl(xs, f(acc, x), f);
  }
}  // list_foldl

inline void * list_foldr(list_t * list, void * acc, fold_f f) {
  if (list == NULL) {
    return acc;
  } else {
    void   * x  = list_head(list);
    list_t * xs = list_tail(list);
    return f(x, list_foldr(xs, acc, f));  // aka "the stack smasher"
  }
}  // list_foldr

inline list_t * list_find(list_t * list, dyn_pred_f pred, void * dep_arg) {
  while (list != NULL) {
    if (pred(list_head(list), dep_arg)) {
      break;
    } else {
      list = list_tail(list);
    }
  }
  return list;
}  // list_find

inline list_t * list_fromarray(void * array, size_t objsize, size_t length) {
  const size_t lsize = sizeof(list_t);
  list_t *     list  = malloc(lsize * length);
  if (list == NULL) {
    size_t req = lsize * length;
    char * units;
    double mem;
    if (req >= 1073741824) {
      units = "GB";
      mem = (double)req / 1073741824.0;
    } else if (req >= 1048576) {
      units = "MB";
      mem = (double)req / 1048576.0;
    } else if (req >= 1024) {
      units = "KB";
      mem = (double)req / 1024.0;
    } else {
      units = "B";
      mem = (double)req;
    }
    fprintf(stderr, "list_fromarray: not enough memory (%.3f %s required)\n",
            mem, units);
    exit(EXIT_FAILURE);
  } else {
    for (size_t i = 0; i < length; i++) {
      list[i].head = (char*)array + i*objsize;
      list[i].tail = i+1 == length ? NULL : &list[i+1];
    }
    return list;
  }
}  // list_fromarray

inline void * list_head(list_t * list) {
  if (list == NULL) {
    fprintf(stderr, "list_head: list is empty\n");
    exit(EXIT_FAILURE);
  } else {
    return list->head;
  }
}  // list_head

inline void list_iter(list_t * list, iter_f f) {
  while (list != NULL) {
    f(list_head(list));
    list = list_tail(list);
  }
}  // list_iter

inline list_t * list_join(list_t * list1, list_t * list2) {
  if (list1 == NULL) {
    return list2;
  } else { 
    last_node(list1)->tail = list2;
    return list1;
  }
}  // list_join

inline size_t list_length(list_t * list) {
  size_t len = 0;
  while (list != NULL) {
    len++;
    list = list_tail(list);
  }
  return len;
}  // list_length

inline list_t * list_map(list_t * list, map_f f) {
  list_t * tmp = list;
  while (tmp != NULL) {
    tmp->head = f(tmp->head);
    tmp = tmp->tail;
  }
  return list;
}  // list_map

inline data_t list_nth(list_t * list, long int n) {
  return list_head(list_skip(list, n));
}  // list_nth

inline lpair_t list_partition(list_t * list, dyn_pred_f pred, void * dep_arg) {
  lpair_t pair = { NULL, NULL };
  while (list != NULL) {
    data_t x = list_head(list);
    list_t * next = list_tail(list);
    if (pred(x, dep_arg)) {
      list->tail = pair.left;
      pair.left = list;
    } else {
      list->tail = pair.right;
      pair.right = list;
    }
    list = next;
  }
  return pair;
}  // list_partition

inline list_t * list_pre(list_t * list, void * data) {
  if (list == NULL) {
    list = list_init();
    list->head = data;
  } else {
    list_t * new_tail = list_cons(list_tail(list), list_head(list));
    list->head = data;
    list->tail = new_tail;
  }
  return list;
}  // list_pre

inline list_t * list_reverse(list_t * list) {
  list_t * reversed = NULL;
  list_t * tmp = list;
  while (list != NULL) {
    tmp        = list_tail(list);
    list->tail = reversed;
    reversed   = list;
    list       = tmp;
  }
  return reversed;
}  // list_reverse

inline list_t * list_skip(list_t * list, long int n) {
  while (n--) list = list_tail(list);
  return list;
}  // list_skip

inline list_t * list_sort(list_t * list, sta_cmp_f lt) {
  if (list == NULL) {
    return NULL;
  } else if (list_tail(list) == NULL) {
    return list;
  } else {
    counter++;
    void * pivot = list_head(list);
    lpair_t part = list_partition(list_tail(list), lt, pivot);
    list->tail = NULL;
    list_t * left  = list_sort(part.left,  lt);
    list_t * right = list_sort(part.right, lt);
    return list_join(left, list_join(list, right));
  }
}  // list_sort

inline list_t * list_tail(list_t * list) {
  if (list == NULL) {
    fprintf(stderr, "list_tail: list is empty\n");
    exit(EXIT_FAILURE);
  } else {
    return list->tail;
  }
}  // list_tail

inline data_t * list_toarray(list_t * list, size_t obj_size) {
  size_t len = list_length(list);
  data_t * array = malloc(obj_size * len);
  for (size_t i = 0; i < len; i++) {
    array[i] = list_head(list);
    list = list_tail(list);
  }
  return array;
}  // list_toarray
