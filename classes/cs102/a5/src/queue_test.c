#include <stdio.h>
#include "../lib/queue.h"

int main(int argc, char *argv[]) {
  printf("\n---------------------\n");
  printf(" TESTING QUEUE\n");
  printf("---------------------\n");

  /* Create a queue */
  printf("\n initializing queue\n");
  queue_t * queue = queue_init();

  /* Check if queue is empty */
  bool empty = queue_isempty(queue);
  printf("  queue empty: %s\n", empty ? "TRUE" : "FALSE");

  /* Check size of queue */
  int size = queue_size(queue);
  printf("  queue size: %d\n", size);

  /* Add a few numbers */
  printf("\n adding 5 numbers\n");
  int numbers[] = { 1, 2, 3, 4, 5 };
  int i;
  for (i = 0; i < 5; i++) {
    queue_enqueue(queue, &numbers[i]);
  }

  /* Check size of queue */
  size = queue_size(queue);
  printf("  queue size: %d\n", size);

  /* Check if queue is empty */
  empty = queue_isempty(queue);
  printf("  queue empty: %s\n", empty ? "TRUE" : "FALSE");

  /* Check the front of queue */
  int front;
  queue_peek(queue, &front);
  printf("  front of queue: %d\n", front);

  /* Delete a few numbers */
  printf("\n deleting some numbers\n");
  queue_dequeue(queue, &front);
  printf("  dequeued: %d\n", front);
  queue_dequeue(queue, &front);
  printf("  dequeued: %d\n", front);

  /* Check the front of queue */
  queue_peek(queue, &front);
  printf("  front of queue: %d\n", front);

  /* Check size of queue */
  size = queue_size(queue);
  printf("  queue size: %d\n", size);

  /* Delete all the numbers */
  printf("\n clearing queue\n");
  queue_clear(queue);

  /* Check if queue is empty */
  empty = queue_isempty(queue);
  printf("  queue empty: %s\n", empty ? "TRUE" : "FALSE");

  /* Check size of queue */
  size = queue_size(queue);
  printf("  queue size: %d\n", size);

  exit(EXIT_SUCCESS);
}

