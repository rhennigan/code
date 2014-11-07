#include <string.h>
#include <stdlib.h>
#include <stdio.h>
#include "../lib/list.h"
#include "../lib/hash.h"

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MIN3(a, b, c) MIN(MIN(a, b), c)

uint64_t hash(void * addr, size_t size) {
  uint64_t hash = 5381;
  uint32_t i, c;
  for (i = 0; i < size; i++)
    c = *(char*)(addr + i);
    printf("*(char*)(addr + i) = %d\n", c);
    hash = ((hash << 5) + hash) + c;
    printf("hash[%d] = %lu\n", i, hash);
  return hash;
}

hash_table_t * hash_table_init(size_t size) {
  hash_table_t * ht = malloc(sizeof(hash_table_t));
  ht_entry_t * data = malloc(sizeof(list_t *) * size);
  ht->size = size;
  ht->row = data;
  uint32_t i;
  for (i = 0; i < size; i++)
    ht->row[i] = NULL;
  return ht;
}

void hash_table_insert(hash_table_t * ht, key_val_t * kv) {
  uint64_t h_idx = hash(kv->key.key, kv->key.size) % ht->size;
  printf("\ninsert h_idx = %ld\n", h_idx);
  list_cons_c(ht->row[h_idx], *kv, key_val_t);
}

bool match_key(void * a1, void * a2) {
  hkey_t k1 = *(hkey_t *)a1;
  hkey_t k2 = *(hkey_t *)a2;
  if (k1.size != k2.size) return false;
  char * str1 = (char *)k1.key;
  char * str2 = (char *)k2.key;
  uint32_t i;
  for (i = 0; i < k1.size; i++)
    if (str1[i] != str2[i]) return false;
  return true;
}

void * hash_table_lookup(hash_table_t * ht, hkey_t key) {
  uint64_t h_idx = hash(key.key, key.size) % ht->size;
  printf("\nlookup h_idx = %ld\n", h_idx);
  void * found = list_find(ht->row[h_idx], &key, &match_key);
  return found;
}

key_val_t * make_kv(void * key, size_t ks, void * val, size_t vs) {
  key_val_t * kv = malloc(sizeof(key_val_t));

  hkey_t k;
  k.size = ks;
  k.key = malloc(k.size);
  memcpy(k.key, key, k.size);
  kv->key = k;

  hval_t v;
  v.size = vs;
  v.val = malloc(v.size);
  memcpy(v.val, val, v.size);
  kv->val = v;

  return kv;
}

/* Levenshtein distance */
uint32_t string_distance(char *s1, char *s2) {
  uint32_t i, j, ld, od;
  uint32_t len1 = strlen(s1);
  uint32_t len2 = strlen(s2);
  uint32_t c[len1+1];
  for (j = 1; j <= len1; j++)
    c[j] = j;
  for (i = 1; i <= len2; i++) {
    c[0] = i;
    for (j = 1, ld = i-1; j <= len1; j++) {
      od = c[j];
      c[j] = MIN3(c[j] + 1, c[j-1] + 1, ld + (s1[j-1] == s2[i-1] ? 0 : 1));
      ld = od;
    }
  }
  return(c[len1]);
}

#undef MIN
#undef MIN3
