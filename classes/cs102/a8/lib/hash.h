#ifndef LIB_HASH_
#define LIB_HASH_

#include <stdint.h>
#include <stdlib.h>
#include <stdbool.h>
#include "./list.h"

#define HASH_TABLE_SIZE 100

typedef struct hkey_s {
  size_t size;
  void * key;
} hkey_t;

typedef struct hval_s {
  size_t size;
  void * val;
} hval_t;

typedef struct key_val_s {
  hkey_t key;
  hval_t val;
} key_val_t;

typedef list_t * ht_entry_t;

typedef struct hash_table_s {
  size_t size;
  ht_entry_t * row;
} hash_table_t;

uint64_t       hash(void * addr, size_t size);
hash_table_t * hash_table_init(size_t size);
void           hash_table_insert(hash_table_t * ht, key_val_t kv);
void *         hash_table_lookup(hash_table_t * ht, hkey_t key);
key_val_t *    make_kv(void * key, size_t ks, void * val, size_t vs);
bool           match_key(key_val_t * kv1, key_val_t * kv2);
uint32_t       string_distance(char *s1, char *s2);

#undef HASH_TABLE_SIZE

#endif  // LIB_HASH_
