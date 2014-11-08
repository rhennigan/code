#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include "lib/user_input.h"
#include "lib/list.h"
#include "lib/hash.h"
#include "lib/util.h"

#define NUMC 240
#define NUMA 333
#define NUMQ 58
#define HTSZ 100

#define MIN(a, b) ((a) < (b) ? (a) : (b))

/* GLOBAL VARIABLES */
char countries[NUMC][BUFSIZ];
char alternate[NUMA][BUFSIZ];
char questions[NUMQ][BUFSIZ];
bool q_answers[NUMC][NUMQ];

int main(int argc, char * argv[]) {
  hash_table_t * hash_table;
  FILE *         ques_file;
  uint32_t       i, j, k;

  hash_table = load_alternates(HTSZ, NUMA, alternate);

  while (1) {
    printf("Enter country name: ");
    char * str = get_input_string();
    char * correct = match_str(str, hash_table, alternate, NUMA);
    printf("closest match for %s: %s\n", str, correct);
  }


  /* uint32_t x = 10, y = 5; */
  /* char * xs = "ten"; */
  /* char * ys = "five"; */

  /* printf("sizeof(xs) = %ld\n", sizeof(xs)); */
  /* printf("sizeof(ys) = %ld\n", sizeof(ys)); */

  /* key_val_t * xk = make_kv(xs, 4, &x, sizeof(x)); */
  /* key_val_t * yk = make_kv(ys, 5, &y, sizeof(y)); */

  /* hash_table_insert(hash_table, xk); */
  /* hash_table_insert(hash_table, yk); */

  /* free(xk); */
  /* free(yk); */

  /* for (i = 0; i < hash_table->size; i++) { */
  /*   list_dump(hash_table->row[i]); */
  /*   list_iter(hash_table->row[i], &print_kv); */
  /* } */

  /* hkey_t k; */
  /* k.key = "ten"; */
  /* k.size = 4; */
  /* void * addr = hash_table_lookup(hash_table, k); */
  /* printf("\n\n%p\n", addr); */

  /* list_iter(hash_table->row[0], &print_kv); */
  /* list_t * list = hash_table->row[0]; */
  /* key_val_t * kv = list_head(list); */
  /* print_kv(kv); */

  /* list_t * list = NULL; */
  /* for (i = 0; i < 10; i++) { */
  /*   list_cons_c(list, i, uint32_t); */
  /* } */

  /* list_iter(list, &print_int); */
  /* printf("\n"); */
  /* list_dump(list); */

  /* uint32_t n = 50; */
  /* void * addr = list_find(list, &n, &equal); */
  /* bool found = addr == NULL ? false : true; */
  /* printf("found: %s\n", found ? "true" : "false"); */

  /* for (i = 0; i < MODSZ; i++) { */
  /*   entry_counts[i] = 0L; */
  /* } */

  /* countries_file = fopen("data/countries.csv", "r"); */

  /* for (i = 0; i < 240; i++) { */
  /*   fgets(countries[i], 32, countries_file); */
  /* } */

  /* while (1) { */
  /*   char * str = get_input_string(); */
  /*   uint32_t dist; */
  /*   uint32_t mindst = INT_MAX; */
  /*   uint32_t minidx = 0; */
  /*   for (i = 0; i < 240; i++) { */
  /*     dist = string_distance(str, countries[i]); */
  /*     if (dist < mindst) { */
  /*       mindst = dist; */
  /*       minidx = i; */
  /*     } */
  /*   } */
  /*   printf("closest match for %s: %s\n", str, countries[minidx]); */
  /* } */

  /* while (fgets(buffer, BUFSIZ, countries_file) != NULL) { */
  /*   entry_counts[hash(buffer) % MODSZ]++; */
  /* } */

  /* for (i = 0; i < MODSZ; i++) { */
  /*   printf("%lu\n", entry_counts[i]); */
  /* } */

  /* fclose(countries_file); */

  return 0;
}

#undef MIN
