#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include "../lib/queue.h"

queue_t * queue_init(void) {
  queue_t * new_queue = malloc(sizeof(queue_t));
  new_queue->list = list_init();
  new_queue->length = 0;
  return new_queue;
}

void queue_enqueue(queue_t * queue, void * data) {
  if (queue_size(queue) == 0) {
    if (!queue->list->length) queue->list = list_init();
    queue->list->head->data = data;
  } else {
    list_append(queue->list, data);
  }
  queue->length += 1;
}

void queue_dequeue(queue_t * queue, void * addr) {
  if (queue_isempty(queue)) {
    perror("queue_dequeue: EMPTY");
    exit(EXIT_FAILURE);
  } else {
    addr_t first = queue->list->head->data;
    memcpy(addr, first, sizeof(first));
    list_delete(queue->list);
    queue->length -= 1;
  }
}

void queue_peek(queue_t * queue, void * addr) {
  if (queue_isempty(queue)) {
    perror("queue_dequeue: EMPTY");
    exit(EXIT_FAILURE);
  } else {
    addr_t first = queue->list->head->data;
    memcpy(addr, first, sizeof(first));
  }
}

void queue_clear(queue_t * queue) {
  list_dispose(queue->list);
  queue->list = list_init();
  queue->length = 0;
}

void queue_dispose(queue_t * queue) {
  list_dispose(queue->list);
  free(queue);
}

bool queue_isempty(queue_t * queue) {
  return queue->length == 0;
}

int queue_size(queue_t * queue) {
  return queue->length;
}
