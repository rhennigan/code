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

bool equal(void * a, void * b) {
  return *(uint32_t*)a == *(uint32_t*)b;
}

int main(int argc, char * argv[]) {
  uint64_t entry_counts[MODSZ];
  char     buffer[BUFSIZ];
  FILE *   countries_file;
  uint32_t i;

  uint32_t x = 10, y = 5;
  char * xs = "ten";
  char * ys = "five";

  key_val_t * xk = make_kv(xs, sizeof(xs), &x, sizeof(x));

  list_t * list = NULL;
  for (i = 0; i < 10; i++) {
    list_cons_c(list, i, uint32_t);
  }

  list_iter(list, &print_int);
  printf("\n");
  list_dump(list);

  uint32_t n = 50;
  void * addr = list_find(list, &n, &equal);
  bool found = addr == NULL ? false : true;
  printf("found: %s\n", found ? "true" : "false");

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
