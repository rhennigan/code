#ifndef LIB_HASH_
#define LIB_HASH_

#include <stdint.h>
#include "./list.h"

#define HASH_TABLE_SIZE 100

typedef struct key_val_s {
  void * key;
  void * val;
} key_val_t;

typedef list_t * ht_entry_t;

typedef struct hash_table_s {
  ht_entry_t row[HASH_TABLE_SIZE];
} hash_table_t;

uint64_t       hash(char * str);
hash_table_t * hash_table_init(uint32_t size);
void           hash_table_insert(hash_table_t * ht, void * item);
void *         hash_table_lookup(hash_table_t * ht, void * item);
uint32_t       string_distance(char *s1, char *s2);

#undef HASH_TABLE_SIZE

#endif  // LIB_HASH_
