#ifndef LIB_UTIL_
#define LIB_UTIL_

#include <stdio.h>
#include <string.h>
#include "./hash.h"

hash_table_t * load_alternates(size_t ht_size, size_t af_size, char ** alts);

#endif  // LIB_UTIL_
