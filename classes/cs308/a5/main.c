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

#define COUNT 50

int main(int argc, char *argv[]) {
  int array[COUNT];
  for (int i = 0; i < COUNT; i++)
    array[i] = rand() % 100;
  list_t * list = list_fromarray(array, sizeof(int), COUNT);

  printf("\n\n\n\n\n\n\n\n\n\n\n");
  list_iter(list, &pint);
  printf("\n\n");
  list_dump(list);

  list_t * sorted = list_sort(list, &intlt);
  printf("\n\n\n\n\n\n\n\n\n\n\n");
  list_iter(sorted, &pint);
  printf("\n\n");
  list_dump(sorted);

  return 0;
}
