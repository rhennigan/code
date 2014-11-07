#include <stdio.h>
#include <stdlib.h>
#include "lib/hash.h"

#define MODSZ 10L

void print_hash(char * str) {
  uint64_t h = hash(str) % MODSZ;
  printf("hash(%s) = %lu\n", str, h);
}

int main(int argc, char * argv[]) {
  uint64_t entry_counts[MODSZ];
  char     buffer[BUFSIZ];
  FILE *   words_file;
  int      i;

  for (i = 0; i < MODSZ; i++) {
    entry_counts[i] = 0L;
  }

  words_file = fopen("words.csv", "r");

  while (fgets(buffer, BUFSIZ, words_file) != NULL) {
    entry_counts[hash(buffer) % MODSZ]++;
  }

  for (i = 0; i < MODSZ; i++) {
    printf("%lu\n", entry_counts[i]);
  }

  fclose(words_file);

  return 0;
}
