#include "lib/list.h"

void pint(void * head) {
  printf(" %d", *(int*)head);
}

void pdouble(void * head) {
  printf(" %f", *(double*)head);
}

int main(int argc, char *argv[]) {
  int array[100];
  for (int i = 0; i < 100; i++) array[i] = (int)i;
  list_t * list = list_fromarray(array, sizeof(int), 100);
  list_iter(list, &pint);
  printf("\n\nsizeof(int) = %lu\nsizeof(double) = %lu",
         sizeof(int), sizeof(double));
  printf("\n\n");
  list_dump(list);
  return 0;
}
