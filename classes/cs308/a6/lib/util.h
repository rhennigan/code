#ifndef _LIB_UTIL_H
#define _LIB_UTIL_H

#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>  /* memset */
#include <stdbool.h>
#include "list.h"
#include "term_color.h"

typedef struct fsys_node_s {
  ino_t          d_ino;
  off_t          d_off;
  unsigned short d_reclen;
  unsigned char  d_type;
  char           d_name[NAME_MAX];
  size_t         depth;
} fsys_node_t;

list_t * dir_list(char * dir_name, size_t depth);
void     display_fs_node(void * node_addr);
bool     name_cmp(void * a, void * b);

#endif  // _LIB_UTIL_H
