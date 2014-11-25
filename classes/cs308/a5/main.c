#include "lib/list.h"

void pl(void * head) {
  printf(" %f", *(double*)head);
}

int main(int argc, char *argv[]) {
  double array[100];
  for (int i = 0; i < 100; i++) array[i] = (double)i;
  list_t * list = list_fromarray(array, sizeof(double), 100);
  list_iter(list, &pl);
  printf("\n\nsizeof(int) = %lul\nsizeof(double) = %d",
         sizeof(int), sizeof(double));
  return 0;
}
