#include "lib/list.h"

int main(int argc, char *argv[]) {
  int array[100];
  for (i = 0; i < 100; i++) array[i] = i * i;
  list_t * list = list_fromarray(array, sizeof(int), 100);
  return 0;
}
