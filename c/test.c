#include "lib/list.h"

#define COUNT 20
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
  list_iter(list1, print);
  printf("\n");
  list_iter(list2, print);
  list_dump(list1);
  list_dump(list2);
  list_t * list = list_join(list1, list2);
  list_iter(list, print);
  list_dump(list);

  TYPE total1 = 0;
  TYPE total2 = 0;
  TYPE total3 = 0;

  total1 = *(TYPE*)list_fold(list, &total1, plus);
  printf("total = %d\n", total1);

  list_dispose(list);
  return 0;
}
