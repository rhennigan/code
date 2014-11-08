#include "../lib/util.h"

hash_table_t * load_alternates(size_t ht_size, char alts[][BUFSIZ]) {
  char           buffer[BUFSIZ];
  FILE *         alts_file;
  hash_table_t * hash_table;
  uint32_t       i, j, k;

  hash_table = hash_table_init(ht_size);
  alts_file  = fopen("data/alternates.csv", "r");

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
    snprintf(alts[i], BUFSIZ, "%s", key);
    key_val_t * kv = make_kv(key, strlen(key)+1, val, strlen(val)+1);
    hash_table_insert(hash_table, kv);
    free(kv);
  }

  fclose(alts_file);
  return hash_table;
}

void load_text(const char * path, size_t len, char array[][BUFSIZ]) {
  FILE * file = fopen(path, "r");
  for (uint32_t i = 0; i < len; i++) {
    fgets(array[i], BUFSIZ, file);
    for (uint32_t j = 0; j < BUFSIZ; j++) {
      if (array[i][j] == '\n')
        array[i][j] = '\0';
    }
  }
  fclose(file);
}

void load_ques(const char * path, size_t qcount, bool questions[][NUMQ]) {
  FILE * file = fopen(path, "r");
  char buff[BUFSIZ];
  for (uint32_t i = 0; i < NUMC; i++) {
    fgets(buff, BUFSIZ, file);
  }
}

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

void dbg_alts(hash_table_t * ht, char alts[][BUFSIZ]) {
  uint32_t i;
  for (i = 0; i < ht->size; i++) {
    list_dump(ht->row[i]);
    printf("\n");
    list_iter(ht->row[i], &print_kv);
  }

  size_t maxlen = 0;
  for (i = 0; i < ht->size; i++) {
    size_t len = list_length(ht->row[i]);
    maxlen = len > maxlen ? len : maxlen;
    printf("%d -> %lu\n", i, len);
  }

  printf("maxlen = %lu\n", maxlen);

  for (i = 0; i < NUMA; i++) {
    printf("%d -> %s\n", i, alts[i]);
  }
}

char * match_str(char * s, hash_table_t * ht, char alts[][BUFSIZ]) {
  uint32_t dist, mindst, minidx, i;
  mindst = INT_MAX;
  minidx = 0;
  for (i = 0; i < NUMA; i++) {
    dist = string_distance(s, alts[i]);
    if (dist < mindst) {
      mindst = dist;
      minidx = i;
    }
  }
  hkey_t k;
  k.size = strlen(alts[minidx])+1;
  k.key = alts[minidx];
  void * addr = hash_table_lookup(ht, k);

  if (addr == NULL) {
    printf("match_str: lookup failure\n");
    exit(EXIT_FAILURE);
  }

  key_val_t kv = *(key_val_t*)addr;
  char * correct = kv.val.val;

  double len = MIN((double)strlen(s), (double)strlen(alts[minidx]));
  double num = MAX(0.0, len - (double)mindst);
  double match = num / len;
  uint32_t md = (int)(100 * match * match);
  printf("matched %s (confidence: %d%%)\n", correct, md);
  return correct;
}
