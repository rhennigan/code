// pq.h - a priority queue based on linked lists
// Copyright (C) 2014 Richard Hennigan

#include <assert.h>
#include <stdio.h>
#include "../lib/pq_heap.h"

#define _L_(n) ( (n) << 1)
#define _R_(n) (((n) << 1) + 1)
#define _U_(n) ( (n) >> 1)

void * pq_dequeue(pq_t * pq);
void   pq_dispose(pq_t * pq);
void   pq_dump(pq_t * pq);
void   pq_enqueue(pq_t * pq, void * obj);
pq_t * pq_init(size_t sz_obj, p_cmp_fun cmp);
bool   pq_isempty(pq_t * pq);
void * pq_peek(pq_t * pq);

#undef _L_
#undef _R_
#undef _U_
