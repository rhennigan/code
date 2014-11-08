#ifndef LIB_UTIL_
#define LIB_UTIL_

#include <limits.h>
#include <stdio.h>
#include <string.h>
#include "./hash.h"

#define NUMA 333

hash_table_t * load_alternates(size_t ht_size, char alts[][BUFSIZ]);
void           print_int(void * addr);
void           print_kv(void * addr);
bool           equal(void * a, void * b);
void           dbg_alts(hash_table_t * ht, char alts[][BUFSIZ]);
char *         match_str(char * s, hash_table_t * ht, char alts[][BUFSIZ]);

#endif  // LIB_UTIL_
