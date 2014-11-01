// pq.h - a priority queue based on linked lists
// Copyright (C) 2014 Richard Hennigan

#include <assert.h>
#include <stdio.h>
#include "../lib/pq.h"

void * pq_dequeue(pq_t * pq) {
  void * h = pq_peek(pq);
  list_t * tmp = pq->list;
  pq->list = list_tail(pq->list);
  free(tmp);
  pq->sz_lst--;
  return h;
}

void pq_dispose(pq_t * pq) {
  if (pq == NULL) return;
  list_dispose(pq->list);
  free(pq);
  pq = NULL;
}

void _pr_addr_(void * head) {
  printf("   %p\n", head);
}

void pq_dump(pq_t * pq) {
  printf("pq_dump: %p\n", pq);
  printf("-----------------\n");
  if (pq == NULL) {
    printf(" NULL\n");
  } else {
    printf(" cmp: ");
    _pr_addr_(pq->cmp);
    printf(" sz_lst: %lu\n", pq->sz_lst);
    printf(" sz_obj: %lu\n", pq->sz_obj);
    printf(" list contents:\n");
    list_iter(pq->list, &_pr_addr_);
    printf("\n");
  }
}

void pq_enqueue(pq_t * pq, void * obj) {
  assert(pq != NULL);

  if (pq->list == NULL || pq->cmp(obj, list_head(pq->list))) {
    pq->list = list_cons(pq->list, obj);
    pq->sz_lst++;
    return;
  }

  list_t * tmp = list_init();
  list_t * prev = tmp;
  prev->tail = pq->list;
  list_t * next = pq->list;

  while (true) {
    if (next == NULL || pq->cmp(obj, list_head(next))) {
      prev->tail = list_cons(next, obj);
      free(tmp);
      pq->sz_lst++;
      return;
    }
    prev = next;
    next = list_tail(next);
  }
}

pq_t * pq_init(size_t sz_obj, p_cmp_fun cmp) {
  pq_t * pq = malloc(sizeof(pq_t));
  assert(pq != NULL);
  pq->list = NULL;
  pq->sz_obj = sz_obj;
  pq->sz_lst = 0;
  pq->cmp = cmp;
  return pq;
}

bool pq_isempty(pq_t * pq) {
  assert(pq != NULL);
  return (pq->sz_lst == 0);
}

void * pq_peek(pq_t * pq) {
  return list_head(pq->list);
}
