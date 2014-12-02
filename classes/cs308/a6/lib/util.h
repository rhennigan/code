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
  ino_t           d_ino;
  off_t           d_off;
  unsigned short  d_reclen;
  unsigned char   d_type;
  char            d_name[NAME_MAX];
  size_t          depth;
  dev_t           st_dev;         /* ID of device containing file */
  ino_t           st_ino;         /* inode number */
  mode_t          st_mode;        /* protection */
  nlink_t         st_nlink;       /* number of hard links */
  uid_t           st_uid;         /* user ID of owner */
  gid_t           st_gid;         /* group ID of owner */
  dev_t           st_rdev;        /* device ID (if special file) */
  off_t           st_size;        /* total size, in bytes */
  blksize_t       st_blksize;     /* blocksize for filesystem I/O */
  blkcnt_t        st_blocks;      /* number of 512B blocks allocated */
  struct timespec st_atim;        /* time of last access */
  struct timespec st_mtim;        /* time of last modification */
  struct timespec st_ctim;        /* time of last status change */
} fsys_node_t;

list_t * dir_list(char * dir_name, size_t depth);
void     display_fs_node(void * node_addr);
bool     name_cmp(void * a, void * b);

#endif  // _LIB_UTIL_H
