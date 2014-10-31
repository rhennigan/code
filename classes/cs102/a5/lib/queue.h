#ifndef _LIB_QUEUE_H_
#define _LIB_QUEUE_H_

#include <stdbool.h>
#include "./list.h"

typedef struct queue_s {
  list_t * list;
  int length;
} queue_t;

typedef char * addr_t;

queue_t * queue_init(void);
void queue_enqueue(queue_t * queue, void * data);
void queue_dequeue(queue_t * queue, void * addr);
void queue_peek(queue_t * queue, void * addr);
void queue_clear(queue_t * queue);
void queue_dispose(queue_t * queue);
bool queue_isempty(queue_t * queue);
int queue_size(queue_t * queue);

#endif
