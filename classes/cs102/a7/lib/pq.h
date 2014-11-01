// pq.h - a priority queue based on linked lists
// Copyright (C) 2014 Richard Hennigan

#ifndef LIB_PQ_H_
#define LIB_PQ_H_

#include <stdlib.h>
#include <stdbool.h>
#include "./list.h"

typedef bool (* p_cmp_fun)(void * a, void * b);

typedef struct pq_s {
  list_t * list;
  size_t sz_lst;
  size_t sz_obj;
  p_cmp_fun cmp;
} pq_t;

void * pq_dequeue(pq_t * pq);
void   pq_dispose(pq_t * pq);
void   pq_dump(pq_t * pq);
void   pq_enqueue(pq_t * pq, void * obj);
pq_t * pq_init(size_t sz_obj, p_cmp_fun cmp);
bool   pq_isempty(pq_t * pq);
void * pq_peek(pq_t * pq);
void   pq_sort(pq_t * pq) { return; }

#endif  // LIB_PQ_H_
