#include "lib/list.h"

void pl(void * head) {
  printf(" %d", *(int*)head);
}

int main(int argc, char *argv[]) {
  int array[100];
  for (int i = 0; i < 100; i++) array[i] = i * i;
  list_t * list = list_fromarray(array, sizeof(int), 100);
  list_iter(list, &pl);
  return 0;
}
