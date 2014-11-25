#include "lib/list.h"

#define MAX_POOL_SIZE (1048576)

void pint(void * head) {
  printf(" %d", *(int*)head);
}

void pdouble(void * head) {
  printf(" %f", *(double*)head);
}

bool intlt(void * a, void * b) {
  return (*(int*)a) <= (*(int*)b);
}

#define COUNT 100

int main(int argc, char *argv[]) {
  printf("\n\n\n\n\n\n\n\n\n\n\n");
  int array[COUNT];
  for (int i = 0; i < COUNT; i++)
    array[i] = rand() % 100;
  list_t * list = list_fromarray(array, sizeof(int), COUNT);
  list_iter(list, &pint);
  printf("\n\nsizeof(int) = %lu\nsizeof(double) = %lu",
         sizeof(int), sizeof(double));
  printf("\n\n");
  list_dump(list);

  printf("\n\n\n\n\n\n\n\n\n\n\n");
  list_t * sorted = list_sort(list, &intlt);
  list_iter(sorted, &pint);
  list_dump(sorted);

  return 0;
}
