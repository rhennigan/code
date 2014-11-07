#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include "lib/user_input.h"
#include "lib/hash.h"

#define MODSZ 50L
#define NUMC 240
#define NUMQ 58

/* GLOBAL VARIABLES */
char countries[NUMC][BUFSIZ];
char questions[NUMQ][BUFSIZ];
bool q_answers[NUMC][NUMQ];

void print_hash(char * str) {
  uint64_t h = hash(str) % MODSZ;
  printf("hash(%s) = %lu\n", str, h);
}

int main(int argc, char * argv[]) {
  uint64_t entry_counts[MODSZ];
  char     buffer[BUFSIZ];
  FILE *   countries_file;
  uint32_t i;

  /* for (i = 0; i < MODSZ; i++) { */
  /*   entry_counts[i] = 0L; */
  /* } */

  countries_file = fopen("data/countries.csv", "r");

  for (i = 0; i < 240; i++) {
    fgets(countries[i], 32, countries_file);
  }

  while (1) {
    char * str = get_input_string();
    uint32_t mindst = INT_MAX;
    uint32_t minidx = 0;
    for (i = 0; i < 240; i++) {
      
    }

  }

  /* while (fgets(buffer, BUFSIZ, countries_file) != NULL) { */
  /*   entry_counts[hash(buffer) % MODSZ]++; */
  /* } */

  /* for (i = 0; i < MODSZ; i++) { */
  /*   printf("%lu\n", entry_counts[i]); */
  /* } */

  fclose(countries_file);

  return 0;
}
