#ifndef LIB_UTIL_H_
#define LIB_UTIL_H_

#include <limits.h>
#include <stdio.h>
#include <string.h>
#include "./hash.h"
#include "./bintree.h"

#define NUMC 240
#define NUMA 333
#define NUMQ 58
#define HTSZ 50

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))

hash_table_t * load_alts(const char * path, size_t hs, char a[][BUFSIZ]);
void           load_text(const char * path, size_t len, char a[][BUFSIZ]);
void           load_answ(const char * path, size_t qc, int32_t a[][NUMQ]);
void           print_int(void * addr);
void           print_kv(void * addr);
void           print_cvec(void * addr);
bool           equal(void * a, void * b);
void           dbg_alts(hash_table_t * ht, char alts[][BUFSIZ]);
char *         match_str(char * s, hash_table_t * ht, char a[][BUFSIZ]);
void           div_tree(bintree_t * bt);

#endif  // LIB_UTIL_H_
