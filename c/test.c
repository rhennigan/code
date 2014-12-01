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

int main(int argc, char *argv[]) {
  uint64_t COUNT = atol(argv[1]);
  TYPE * array = malloc(sizeof(TYPE) * COUNT);
  assert(array != NULL);

  clock_t start = clock(), diff;
  for (TYPE i = 0; i < COUNT; i++) {
    array[i] = i;
  }
  diff = clock() - start;
  int msec = diff * 1000 / CLOCKS_PER_SEC;
  printf("fill array time = %d seconds %d milliseconds\n", msec/1000, msec%1000);

  start = clock();
  list_t * list = list_fromarray(array, sizeof(TYPE), COUNT);
  diff = clock() - start;
  msec = diff * 1000 / CLOCKS_PER_SEC;
  printf("fill list time = %d seconds %d milliseconds\n", msec/1000, msec%1000);

  TYPE total1 = 0;
  TYPE total2 = 0;
  TYPE total3 = 0;

  start = clock();
  total1 = *(TYPE*)list_fold(list, &total1, plus);
  diff = clock() - start;
  msec = diff * 1000 / CLOCKS_PER_SEC;
  printf("fill list time = %d seconds %d milliseconds\n", msec/1000, msec%1000);

  start = clock();
  total2 = *(TYPE*)list_fold(list, &total2, plus);
  diff = clock() - start;
  msec = diff * 1000 / CLOCKS_PER_SEC;
  printf("fill list time = %d seconds %d milliseconds\n", msec/1000, msec%1000);

  start = clock();
  total3 = *(TYPE*)list_fold(list, &total3, plus);
  diff = clock() - start;
  msec = diff * 1000 / CLOCKS_PER_SEC;
  printf("fill list time = %d seconds %d milliseconds\n", msec/1000, msec%1000);

  free(list);
  return 0;
}
