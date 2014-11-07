#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include "lib/user_input.h"
#include "lib/list.h"
#include "lib/hash.h"

#define MODSZ 50L
#define NUMC 240
#define NUMA 331
#define NUMQ 58
#define HTSZ 100

#define MIN(a, b) ((a) < (b) ? (a) : (b))

/* GLOBAL VARIABLES */
char countries[NUMC][BUFSIZ];
char alternate[NUMA][BUFSIZ];
char questions[NUMQ][BUFSIZ];
bool q_answers[NUMC][NUMQ];

/* void print_hash(char * str) { */
/*   uint64_t h = hash(str) % MODSZ; */
/*   printf("hash(%s) = %lu\n", str, h); */
/* } */

void print_int(void * addr) {
  printf(" %d", *(int*)addr);
}

void print_kv(void * addr) {
  key_val_t kv = *(key_val_t *)addr;
  char * key = malloc(kv.key.size);
  memcpy(key, kv.key.key, kv.key.size);
  char * val = malloc(kv.val.size);
  memcpy(val, kv.val.val, kv.val.size);
  printf("  (%s, %s)\n", key, val);
}

bool equal(void * a, void * b) {
  return *(uint32_t*)a == *(uint32_t*)b;
}

int main(int argc, char * argv[]) {
  /* uint64_t entry_counts[MODSZ]; */
  char     buffer[BUFSIZ];
  FILE *   alts_file;
  uint32_t i, j, k;

  hash_table_t * hash_table = hash_table_init(HTSZ);

  alts_file = fopen("data/alternates.csv", "r");

  for (i = 0; i < NUMA; i++) {
    fgets(buffer, BUFSIZ, alts_file);
    char * key = malloc(BUFSIZ);
    char * val = malloc(BUFSIZ);
    memset(key, '\0', BUFSIZ);
    memset(val, '\0', BUFSIZ);
    for (j = 0; j < BUFSIZ; j++) {
      if (buffer[j] == ',') {
        key[j] = '\0';
        break;
      }
      key[j] = buffer[j];
    }
    for (k = j + 1; k < BUFSIZ; k++) {
      if (buffer[k] == '\n') {
        val[k-j-1] = '\0';
        break;
      }
      val[k-j-1] = buffer[k];
      if (buffer[k] == '\0') break;
    }
    snprintf(alternate[i], BUFSIZ, "%s", key);
    printf("key = %s (%lu), val = %s (%lu)\n",
           key, strlen(key), val, strlen(val));
    key_val_t * kv = make_kv(key, strlen(key)+1, val, strlen(val)+1);
    hash_table_insert(hash_table, kv);
    free(kv);
  }

  /* for (i = 0; i < hash_table->size; i++) { */
  /*   list_dump(hash_table->row[i]); */
  /*   printf("\n"); */
  /*   list_iter(hash_table->row[i], &print_kv); */
  /* } */

  size_t maxlen = 0;
  for (i = 0; i < hash_table->size; i++) {
    size_t len = list_length(hash_table->row[i]);
    maxlen = len > maxlen ? len : maxlen;
    printf("%d -> %lu\n", i, len);
  }

  printf("maxlen = %lu\n", maxlen);

  for (i = 0; i < NUMA; i++) {
    printf("%d -> %s\n", i, alternate[i]);
  }


  while (1) {
    printf("Enter country name: ");
    char * str = get_input_string();
    uint32_t dist;
    uint32_t mindst = INT_MAX;
    uint32_t minidx = 0;
    for (i = 0; i < NUMA; i++) {
      dist = string_distance(str, alternate[i]);
      if (dist < mindst) {
        mindst = dist;
        minidx = i;
      }
    }
    hkey_t k;
    k.size = strlen(alternate[minidx])+1;
    k.key = alternate[minidx];
    void * addr = hash_table_lookup(hash_table, k);
    key_val_t kv = *(key_val_t*)addr;
    char * correct = kv.val.val;
    printf("\n\nlookup = %p\n", addr);
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
