// pq_heap.c - a priority queue based on heaps
// Copyright (C) 2014 Richard Hennigan

#include <assert.h>
#include <stdio.h>
#include "../lib/pq_heap.h"

#define _L(n) (((n) << 1) + 1)  // 2n + 1
#define _R(n) (((n) << 1) + 2)  // 2n + 2
#define _U(n) ((n - 1) >> 1)    // floor((n - 1) / 2)

#define _SWAP(a, b) do {                        \
    register void * t = (a);                    \
    (a) = (b);                                  \
    (b) = t;                                    \
  } while (0);

#define HEAP_SIZE 1024

size_t maxc(pq_t * pq, size_t n) {
  size_t l = _L(n);
  if (l >= pq->sz_lst) return 0;
  size_t r = _R(n);
  if (r >= pq->sz_lst) return l;
  return (pq->cmp(pq->list[l], pq->list[r]) ? l : r);
}

void sift_down(pq_t * pq, size_t n) {
  size_t ch = maxc(pq, n);
  if (ch && pq->cmp(pq->list[ch], pq->list[n])) {
    _SWAP(pq->list[ch], pq->list[n]);
    sift_down(pq, ch);
  } else {
    return;
  }
}

void sift_up(pq_t * pq, size_t n) {
  if (!n) {
    return;
  } else {
    size_t p = _U(n);
    if (pq->cmp(pq->list[n], pq->list[p])) {
      _SWAP(pq->list[n], pq->list[p]);
      sift_up(pq, p);
    }
  }
}

void * pq_dequeue(pq_t * pq) {
  void * head = pq->list[0];
  pq->sz_lst--;
  pq->sz_avl++;
  pq->list[0] = pq->list[pq->sz_lst - 1];
  sift_down(pq, 0);
  return head;
}

void pq_dispose(pq_t * pq) {
  free(pq->list);
  pq->list = NULL;
  free(pq);
  pq = NULL;
}

void pq_dump(pq_t * pq);

void pq_enqueue(pq_t * pq, void * obj) {
  assert(pq->sz_avl);
  pq->list[pq->sz_lst] = obj;
  pq->sz_lst++;
  pq->sz_avl--;  // TODO(rhennigan): realloc heap if space runs out
}

pq_t * pq_init(size_t sz_obj, p_cmp_fun cmp) {
  pq_t * pq = malloc(sizeof(pq_t));
  assert(pq != NULL);

  pq->list = malloc(HEAP_SIZE * sz_obj);
  assert(pq->list != NULL);

  pq->sz_lst = 0;
  pq->sz_obj = sz_obj;
  pq->sz_avl = HEAP_SIZE;
  pq->cmp = cmp;

  return pq;
}

bool pq_isempty(pq_t * pq) {
  return pq->sz_lst;
}

void * pq_peek(pq_t * pq) {
  return pq->list[0];
}

#undef _L
#undef _R
#undef _U
#undef _SWAP
