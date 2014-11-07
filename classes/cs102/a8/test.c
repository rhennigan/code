#include <stdio.h>
#include "lib/hash.h"

#define MODSZ 10L

void print_hash(char * str) {
  uint64_t h = hash(str) % MODSZ;
  printf("hash(%s) = %lu\n", str, h);
}

int main(int argc, char * argv[]) {
  uint64_t entry_counts[MODSZ];
  int i;

  for (i = 0; i < MODSZ; i++) {
    entry_counts[i] = 0L;
  }

  for (i = 1; i < argc; i++) {
    print_hash(argv[i]);
    entry_counts[hash(argv[i]) % MODSZ]++;
  }

  for (i = 0; i < MODSZ; i++) {
    printf("%lu\n", entry_counts[i]);
  }


  return 0;
}
