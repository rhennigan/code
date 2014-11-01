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

size_t maxc(pq_t * pq, size_t n, size_t end) {
  size_t l = _L(n);
  if (l >= end) return 0;
  size_t r = _R(n);
  if (r >= end) return l;
  return (pq->cmp(pq->list[l], pq->list[r]) ? l : r);
}

void sift_down(pq_t * pq, size_t n, size_t end) {
  size_t ch = maxc(pq, n, end);
  if (ch && pq->cmp(pq->list[ch], pq->list[n])) {
    _SWAP(pq->list[ch], pq->list[n]);
    sift_down(pq, ch, end);
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
  pq->list[0] = pq->list[pq->sz_lst];
  sift_down(pq, 0, pq->sz_lst);
  return head;
}

void pq_dispose(pq_t * pq) {
  free(pq->list);
  pq->list = NULL;
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
    printf(" sz_avl: %lu\n", pq->sz_avl);
    printf(" sz_obj: %lu\n", pq->sz_obj);
    printf(" list contents:\n");
    unsigned int i;
    for (i = 0; i < pq->sz_lst; i++) {
      _pr_addr_(pq->list[i]);
    }
    printf("\n");
  }
}

void pq_enqueue(pq_t * pq, void * obj) {
  // TODO(rhennigan): realloc heap if space runs out
  assert(pq->sz_avl);
  pq->list[pq->sz_lst] = obj;
  sift_up(pq, pq->sz_lst);
  pq->sz_lst++;
  pq->sz_avl--;
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

#define _MAX(a, b) ((a) > (b) ? (a) : (b))

void pq_sort(pq_t * pq) {
  int start;
  for (start = _U(pq->sz_lst - 1); start >= 0; start--) {
    sift_down(pq, start, pq->sz_lst - 1);
  }

  int end;
  for (end = pq->sz_lst - 1; end > 0; end--) {
    _SWAP(pq->list[0], pq->list[end]);
    sift_down(pq, 0, end);
  }

  unsigned int i;
  for (i = 0; i <= (_MAX(pq->sz_lst / 2, 1) - 1); i++) {
    _SWAP(pq->list[i], pq->list[pq->sz_lst - i - 1]);
  }
}

#undef _L
#undef _R
#undef _U
#undef _SWAP
