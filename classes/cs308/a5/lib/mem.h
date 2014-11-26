// mem.h

#ifndef LIB_MEM_H_
#define LIB_MEM_H_

#include <string.h>
#include "./list.h"

/******************************************************************************/
/* CONFIG OPTIONS                                                             */
/******************************************************************************/
#define MAX_POOL_SIZE_MBYTES  (1024ul)
#define MIN_ALLOC_BYTES       (32ul)
#define MAX_HISTORY_LENGTH    (1000ul)

/******************************************************************************/
#define MAX_POOL_SIZE_BYTES   (1048576ul * MAX_POOL_SIZE_MBYTES)
#define WORD_SIZE_BYTES       (sizeof(void *))
#define MAX_POOL_SIZE_WORDS   (MAX_POOL_SIZE_BYTES / WORD_SIZE_BYTES)
#define MIN_ALLOC_WORDS       (MIN_ALLOC_BYTES / WORD_SIZE_BYTES)

/******************************************************************************/
/* TYPES                                                                      */
/******************************************************************************/
typedef enum { FIRST_FIT, BEST_FIT, BUDDY_SYSTEM } policy_t;

typedef struct alloc_status_s {
  size_t total_bytes_free;
  size_t max_bytes_free;
  size_t       num_blocks;
  unsigned int request_num;
} alloc_status_t;

typedef struct mem_block_s {
  int    owner;    // would likely be a pid in a real setting
  bool   is_free;
  void * addr;     // base address of block
  size_t size;     // in words
} mem_block_t;

/******************************************************************************/
/* GLOBALS                                                                    */
/******************************************************************************/
extern list_t * memory_free;
extern void   * memory_pool[];

/******************************************************************************/
void print_usage(char * name);
void print_mem_config();

#endif  // LIB_MEM_H_
