#ifndef LIB_HASH_
#define LIB_HASH_

#include <stdint.h>
#include <stdbool.h>
#include "./list.h"

#define HASH_TABLE_SIZE 100

typedef struct key_val_s {
  uint32_t key_size;
  void *   key;
  void *   val;
} key_val_t;

typedef list_t * ht_entry_t;

typedef struct hash_table_s {
  uint32_t size;
  ht_entry_t * row;
} hash_table_t;

uint64_t       hash(char * str);
hash_table_t * hash_table_init(uint32_t size);
void           hash_table_insert(hash_table_t * ht, key_val_t kv);
void *         hash_table_lookup(hash_table_t * ht, void * key);
key_val_t *    make_kv(void * key, void * val);
bool           match_key(key_val_t * kv1, key_val_t * kv2);
uint32_t       string_distance(char *s1, char *s2);

#undef HASH_TABLE_SIZE

#endif  // LIB_HASH_
