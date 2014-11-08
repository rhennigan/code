#ifndef LIB_UTIL_
#define LIB_UTIL_

#include <limits.h>
#include <stdio.h>
#include <string.h>
#include "./hash.h"

hash_table_t * load_alternates(size_t ht_size, size_t as, char alts[][BUFSIZ]);
void           print_int(void * addr);
void           print_kv(void * addr);
bool           equal(void * a, void * b);
void           dbg_alts(hash_table_t * ht, char ** alts, size_t a_size);
char *         match_str(char * s, hash_table_t * ht, char ** alts, size_t as);

#endif  // LIB_UTIL_
