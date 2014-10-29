// lib/deque.h - Copyright 2014, Richard Hennigan

#ifndef LIB_DEQUE_H_
#define LIB_DEQUE_H_

#include <stdbool.h>
#include "./list.h"
#include "./types.h"

typedef list_t deque_t;

deque_t * deque_init(void);
void deque_clear(deque_t * deque);

void deque_peekf(deque_t * deque, void * addr, size_t size);
void deque_peekr(deque_t * deque, void * addr, size_t size);

void deque_dequeuef(deque_t * deque, void * addr, size_t size);
void deque_dequeuer(deque_t * deque, void * addr, size_t size);

void deque_enqueuef(deque_t * deque, void * data);
void deque_enqueuer(deque_t * deque, void * data);

void deque_dispose(deque_t * deque);
bool deque_isempty(deque_t * deque);
int deque_size(deque_t * deque);

#endif  // LIB_DEQUE_H_
