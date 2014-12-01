#include <time.h>
#include "lib/list.h"

#define COUNT 1000000
#define TYPE int
#define FMT "%d"

void print(data_t head) {
  printf(FMT" ", *(TYPE*)head);
}

void * plus(void * acc, data_t head) {
  *(TYPE*)acc += *(TYPE*)head;
  return acc;
}

int main(int argc, char *argv[]) {
  TYPE array1[COUNT];
  TYPE array2[COUNT];
  for (TYPE i = 0; i < COUNT; i++) {
    array1[i] = i;
    array2[i] = COUNT + i;
  }
  list_t * list1 = list_fromarray(array1, sizeof(TYPE), COUNT);
  list_t * list2 = list_fromarray(array2, sizeof(TYPE), COUNT);
  list_t * list = list_join(list1, list2);

  TYPE total1 = 0;
  TYPE total2 = 0;
  TYPE total3 = 0;

  int start1 = time(NULL);
  total1 = *(TYPE*)list_fold(list, &total1, plus);
  int time1 = time(NULL) - start1;

  total2 = *(TYPE*)list_foldl(list, &total2, plus);
  total3 = *(TYPE*)list_foldr(list, &total3, plus);

  printf("total1 = %d, time1 = %d\n", total1, time1);
  printf("total2 = %d\n", total2);
  printf("total3 = %d\n", total3);

  list_dispose(list);
  return 0;
}
