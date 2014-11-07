#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include "lib/user_input.h"
#include "lib/list.h"
#include "lib/hash.h"

#define MODSZ 50L
#define NUMC 240
#define NUMQ 58

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define COPY(i, t) do {                         \
    t * n = malloc(sizeof(t));                  \
    *n = i;                                     \
  } while (0)

/* GLOBAL VARIABLES */
char countries[NUMC][BUFSIZ];
char questions[NUMQ][BUFSIZ];
bool q_answers[NUMC][NUMQ];

void print_hash(char * str) {
  uint64_t h = hash(str) % MODSZ;
  printf("hash(%s) = %lu\n", str, h);
}

void print_int(void * addr) {
  printf(" %d", *(int*)addr);
}

int main(int argc, char * argv[]) {
  uint64_t entry_counts[MODSZ];
  char     buffer[BUFSIZ];
  FILE *   countries_file;
  uint32_t i;

  list_t * list = NULL;
  for (i = 0; i < 10; i++) {
    uint32_t * n = malloc(sizeof(uint32_t));
    *n = i;
    list = list_cons(list, n);
  }

  list_iter(list, &print_int);
  printf("\n");
  list_dump(list);

  /* for (i = 0; i < MODSZ; i++) { */
  /*   entry_counts[i] = 0L; */
  /* } */

  countries_file = fopen("data/countries.csv", "r");

  for (i = 0; i < 240; i++) {
    fgets(countries[i], 32, countries_file);
  }

  while (1) {
    char * str = get_input_string();
    uint32_t dist;
    uint32_t mindst = INT_MAX;
    uint32_t minidx = 0;
    for (i = 0; i < 240; i++) {
      dist = string_distance(str, countries[i]);
      if (dist < mindst) {
        mindst = dist;
        minidx = i;
      }
    }
    printf("closest match for %s: %s\n", str, countries[minidx]);
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

#undef MIN
