// main.c

#include <limits.h>
#include "lib/mem.h"

enum { CT_POUND, CT_PREPROC, CT_PREPROC_BODY, CT_PP };

const char *token_names[] =
{
   [CT_POUND]        = "POUND",
   [CT_PREPROC]      = "PREPROC",
   [CT_PREPROC_BODY] = "PREPROC_BODY",
   [CT_PP]           = "PP",
};

int main(int argc, char *argv[]) {
  /****************************************************************************/
  /* READ COMMAND LINE ARGUMENTS                                              */
  /****************************************************************************/
  if (argc != 4) {
    print_usage(argv[0]);
    exit(EXIT_FAILURE);
  }  // end if (argc != 4)

  FILE * req_file;

  /* get policy */
  if (strcmp(argv[1], "first") == 0) {
    policy = FIRST_FIT;
  } else if (strcmp(argv[1], "best") == 0) {
    policy = BEST_FIT;
  } else if (strcmp(argv[1], "buddy") == 0) {
    policy = BUDDY_SYSTEM;
  } else {  // unknown policy name
    print_usage(argv[0]);
    exit(EXIT_FAILURE);
  }  // end if (strcmp(argv[1], "first") == 0)

  /* get pool size */
  if (!atoi(argv[2])) {
    printf("error: the pool size must be a positive integer\n");
    exit(EXIT_FAILURE);
  } else if ((size_t)atoi(argv[2]) > MAX_POOL_SIZE_KBYTES) {
    printf("error: the pool size exceeds the maximum of %lu KB\n",
           MAX_POOL_SIZE_KBYTES);
    exit(EXIT_FAILURE);
  } else {  // given pool size is greater than 0
    pool_size = atoi(argv[2]);
  }  // end if (!atoi(argv[2]))

  /* open requests file for reading */
  req_file = fopen(argv[3], "r");

  /****************************************************************************/
  /* SETUP MEMORY POOL                                                        */
  /****************************************************************************/
  mem_block_t init_block;
  init_block.id      = NOBODY;
  init_block.is_free = true;
  init_block.addr    = memory_pool;
  init_block.size    = BYTES_TO_WORDS(pool_size);
  init_block.prev    = NULL;
  memory_block_list  = list_pre(NULL, &init_block);
  init_block.curr    = memory_block_list;

  req_status_t init_req_status;
  init_req_status.req_id       = init_block.id;
  init_req_status.req_type     = NONE;
  init_req_status.req_size     = 0;
  init_req_status.req_granted  = true;
  init_req_status.req_addr     = memory_pool;
  init_req_status.total_free   = init_block.size;
  init_req_status.max_free     = init_block.size;
  init_req_status.blocks_free  = 1;
  init_req_status.blocks_alloc = 0;
  req_history[0]               = init_req_status;

  print_mem_config();
  print_output(0, 0);

  /****************************************************************************/
  /* LOAD AND PROCESS REQUESTS                                                */
  /****************************************************************************/
  request_t * request = load_request(req_file);
  
  printf("test: %s\n", token_names[CT_POUND]);
  /****************************************************************************/
  /* CLEAN UP                                                                 */
  /****************************************************************************/
  fclose(req_file);
  exit(EXIT_SUCCESS);
}


