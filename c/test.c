#include <time.h>
#include <stdint.h>
#include "lib/list.h"

// #define COUNT 100000
#define TYPE uint64_t
#define FMT "%lu"

void print(data_t head) {
  printf(FMT" ", *(TYPE*)head);
}

void * plus(void * acc, data_t head) {
  *(TYPE*)acc += *(TYPE*)head;
  return acc;
}

#define TIMING(action, label) do {                              \
  start = clock();                                              \
  action;                                                       \
  diff = clock() - start;                                       \
  msec = diff * 1000 / CLOCKS_PER_SEC;                          \
  printf("%s = %d.%d\n", label, msec/1000, msec%1000);          \
  } while (0);

int main(int argc, char *argv[]) {
  clock_t start, diff;
  int msec;
  uint64_t COUNT = atol(argv[1]);
  
  printf("array size = %lu\n", sizeof(TYPE) * COUNT);
  printf("list size = %lu\n", sizeof(list_t) * COUNT);
  
  TIMING(
  TYPE * array = malloc(sizeof(TYPE) * COUNT);
  assert(array != NULL);
  for (TYPE i = 0; i < COUNT; i++) {
    array[i] = rand() % COUNT;
  }, "fill array time");

  start = clock();
  list_t * list = list_fromarray(array, sizeof(TYPE), COUNT);
  diff = clock() - start;
  msec = diff * 1000 / CLOCKS_PER_SEC;
  printf("fill list time  = %d.%d\n", msec/1000, msec%1000);

  TYPE total = 0;

  start = clock();
  total = *(TYPE*)list_fold(list, &total, plus);
  diff = clock() - start;
  msec = diff * 1000 / CLOCKS_PER_SEC;
  printf("list_fold time  = %d.%d\n\n", msec/1000, msec%1000);
  printf("list_fold total = %lu\n", total);

  free(array);
  free(list);
  return 0;
}
