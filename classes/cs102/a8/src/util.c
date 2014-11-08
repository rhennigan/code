#include "../lib/util.h"

hash_table_t * load_alternates(size_t ht_size, size_t af_size, char ** alts) {
  char           buffer[BUFSIZ];
  FILE *         alts_file;
  hash_table_t * hash_table;
  uint32_t       i, j, k;

  hash_table = hash_table_init(ht_size);
  alts_file  = fopen("data/alternates.csv", "r");

  for (i = 0; i < af_size; i++) {
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
    printf("key = %s (%lu), val = %s (%lu)\n",
           key, strlen(key), val, strlen(val));
    key_val_t * kv = make_kv(key, strlen(key)+1, val, strlen(val)+1);
    hash_table_insert(hash_table, kv);
    free(kv);
  }

  fclose(alts_file);
  return hash_table;
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

void dbg_alts(hash_table_t * ht, char ** alts, size_t a_size) {
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

  for (i = 0; i < a_size; i++) {
    printf("%d -> %s\n", i, alts[i]);
  }
}
