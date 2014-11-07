#ifndef LIB_HASH_
#define LIB_HASH_

#include <stdint.h>
#include "./list.h"

typedef struct key_val_s {
  void * key;
  void * val;
} key_val_t;

typedef struct hash_table_s {
  list_t * entries[];
} hash_table_t;

uint64_t       hash(char * str);
hash_table_t * hash_table_init(uint32_t size);
uint32_t       string_distance(char *s1, char *s2);

#endif  // LIB_HASH_
