#include <stdio.h>
#include "lib/hash.h"

int main(int argc, char * argv[]) {
  char * str = argv[1];
  uint64_t h = hash(str);
  printf("hash(%s) = %lu\n", str, h);
  return 0;
}
