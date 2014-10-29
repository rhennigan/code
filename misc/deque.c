// src/deque.c - Copyright 2014, Richard Hennigan

#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include "../lib/deque.h"

deque_t * deque_init(void) {
  return list_init();
}

void deque_clear(deque_t * deque) {
  deque_dispose(deque);
  deque = deque_init();
}

void deque_peekf(deque_t * deque, void * addr, size_t size) {
  if (deque_isempty(deque)) {
    perror("deque_peekf: EMPTY");
    exit(EXIT_FAILURE);
  } else {
    addr_t first = deque->head->data;
    memcpy(addr, first, size);
  }
}

void deque_peekr(deque_t * deque, void * addr, size_t size) {
  if (deque_isempty(deque)) {
    perror("deque_peekr: EMPTY");
    exit(EXIT_FAILURE);
  } else {
    addr_t last = deque->tail->data;
    memcpy(addr, last, size);
  }
}

void deque_dequeuef(deque_t * deque, void * addr, size_t size) {
  if (deque_isempty(deque)) {
    perror("deque_dequeuef: EMPTY");
    exit(EXIT_FAILURE);
  } else {
    addr_t first = deque->head->data;
    memcpy(addr, first, size);
    list_delf(deque);
  }
}

void deque_dequeuer(deque_t * deque, void * addr, size_t size) {
  if (deque_isempty(deque)) {
    perror("deque_dequeuef: EMPTY");
    exit(EXIT_FAILURE);
  } else {
    addr_t last = deque->tail->data;
    memcpy(addr, last, size);
    list_delr(deque);
  }
}

void deque_enqueuef(deque_t * deque, void * data) {
  list_insf(deque, data);
}

void deque_enqueuer(deque_t * deque, void * data) {
  list_insr(deque, data);
}

void deque_dispose(deque_t * deque) {
  list_dispose(deque);
}

bool deque_isempty(deque_t * deque) {
  return deque->length == 0;
}

int deque_size(deque_t * deque) {
  return deque->length;
}
