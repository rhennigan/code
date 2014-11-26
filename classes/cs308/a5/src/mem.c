// mem.c

#include "../lib/mem.h"

/******************************************************************************/
/* GLOBAL DEFINITIONS                                                         */
/******************************************************************************/
list_t *     memory_block_list = NULL;
void *       memory_pool[MAX_POOL_SIZE_WORDS];
req_status_t req_history[MAX_HISTORY_LENGTH];
policy_t     policy;
bytes_t      pool_size;

/******************************************************************************/
static inline void hline() {
  printf("/");
  for (int i = 0; i < 78; i++)
    printf("*");
  printf("/");
}

void print_usage(char * name) {
  printf("error reading arguments\n");
  printf("usage:\n");
  printf("%s ", name);
  printf("[policy:(first|best|buddy)] ");
  printf("[pool_size:int] ");
  printf("[req_file:string]\n");
}

/* Debugging info */
void print_mem_config() {
  printf("MAX_POOL_SIZE_BYTES = %lu\n", MAX_POOL_SIZE_BYTES);
  printf("MIN_ALLOC_BYTES     = %lu\n", MIN_ALLOC_BYTES);
  printf("MAX_POOL_SIZE_WORDS = %lu\n", MAX_POOL_SIZE_WORDS);
  printf("MIN_ALLOC_WORDS     = %lu\n", MIN_ALLOC_WORDS);
  printf("
/******************************************************************************/
/* CONFIG OPTIONS                                                             */
/******************************************************************************/
MAX_POOL_SIZE_MBYTES  (1024ul)
MIN_ALLOC_BYTES       (32ul)
MAX_HISTORY_LENGTH    (1000ul)

/******************************************************************************/
MAX_POOL_SIZE_BYTES   (1048576ul * MAX_POOL_SIZE_MBYTES)
WORD_SIZE_BYTES       (sizeof(void *))
MAX_POOL_SIZE_WORDS   (MAX_POOL_SIZE_BYTES / WORD_SIZE_BYTES)
MIN_ALLOC_WORDS       (MIN_ALLOC_BYTES / WORD_SIZE_BYTES)
");
}
