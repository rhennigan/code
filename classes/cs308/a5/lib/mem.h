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

/* Type aliases to make units clear */
typedef size_t bytes_t;
typedef size_t words_t;

/* For specifying the type of memory management requests */
typedef enum { ALLOC, FREE } req_t;
typedef struct request_s {
  int     id;
  req_t   type;
  bytes_t size;
} request_t;

typedef struct alloc_status_s {
  bytes_t total_free;
  bytes_t total_alloc;
  bytes_t max_free;
  bytes_t max_alloc;
  size_t  total_blocks;
  int     request_num;
} alloc_status_t;

typedef struct mem_block_s {
  int     owner;    // would likely be a pid in a real setting
  bool    is_free;
  void  * addr;     // base address of block
  words_t size;
} mem_block_t;

/******************************************************************************/
/* GLOBALS                                                                    */
/******************************************************************************/
extern list_t * memory_block_list;      // elements have type mem_block_t*
extern void   * memory_pool[];
extern alloc_status_t alloc_history[];  // for printing output

/******************************************************************************/
void print_usage(char * name);
void print_mem_config();

#endif  // LIB_MEM_H_
