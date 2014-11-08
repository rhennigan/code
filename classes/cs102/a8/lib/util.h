#ifndef LIB_UTIL_
#define LIB_UTIL_

#include <stdio.h>
#include <string.h>
#include "./hash.h"

hash_table_t * load_alternates(size_t ht_size, size_t af_size, char ** alts);
void           print_int(void * addr);
void           print_kv(void * addr);
bool           equal(void * a, void * b);
void           dbg_alts(hash_table_t * ht, char ** alts, size_t alts_size);
char *         match_str(char * str, char ** alts, hash_table_t * ht);

#endif  // LIB_UTIL_
