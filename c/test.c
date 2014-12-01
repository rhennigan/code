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
  for (TYPE i = 0; i < COUNT; i++) {
    array[i] = i;
  }
  list_t * list = list_fromarray(array, sizeof(TYPE), COUNT);

  TYPE total1 = 0;
  TYPE total2 = 0;
  TYPE total3 = 0;

  int start1 = time(NULL);
  total1 = *(TYPE*)list_fold(list, &total1, plus);
  int time1 = time(NULL) - start1;

  int start2 = time(NULL);
  total2 = *(TYPE*)list_fold(list, &total2, plus);
  int time2 = time(NULL) - start2;

  int start3 = time(NULL);
  total3 = *(TYPE*)list_fold(list, &total3, plus);
  int time3 = time(NULL) - start3;

  printf("total1 = %lu, time1 = %d\n", total1, time1);
  printf("total2 = %lu, time2 = %d\n", total2, time2);
  printf("total3 = %lu, time3 = %d\n", total3, time3);

  list_dispose(list);
  return 0;
}
