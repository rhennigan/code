// main.c

#include <limits.h>
#include "lib/mem.h"

void check_links() {
  list_t * prev = NULL;
  list_t * curr = memory_block_list;
  list_t * next = list_tail(curr);
  while (1) {
    mem_block_t * cblock = block_from_list(curr);
    mem_block_t * nblock = block_from_list(next);
    cblock->prev = prev;
    cblock->curr = curr;
    cblock->next = next;
    int64_t caddr = cblock ? rel_addr(cblock->addr) : -1;
    int64_t naddr = nblock ? rel_addr(nblock->addr) : -1;
    /* int64_t caddr = curr ? rel_addr(block_from_list(curr)->addr) : -1; */
    /* int64_t naddr = next ? rel_addr(block_from_list(next)->addr) : -1; */
    int64_t nsize = nblock ? (int64_t)nblock->size : -1;
    bool pair = policy != BUDDY_SYSTEM || (int64_t)(caddr ^ nsize) == naddr;
    bool cfree = cblock ? cblock->is_free : false;
    bool nfree = nblock ? nblock->is_free : false;
    /* bool cfree = curr ? block_from_list(curr)->is_free : false; */
    /* bool nfree = next ? block_from_list(next)->is_free : false; */
    bool merge = pair && cfree && nfree;

    if (merge) {
      cblock->size += nblock->size;
      cblock->next = list_tail(next);
      curr->tail = list_tail(next);
      if (next && list_head(next)) free(list_head(next));
      if (next) free(next);
      check_links();
      return;
    }

    /* printf("%s%ld -> %ld: xor = %ld, addr = %ld\n", */
    /*        merge ? C_GREEN : C_RESET, */
    /*        WORDS_TO_BYTES(caddr), WORDS_TO_BYTES(naddr), */
    /*        caddr ^ cblock->size, naddr); */
    if (next == NULL) break;
    prev = curr;
    curr = next;
    next = list_tail(next);
  }
}

int main(int argc, char *argv[]) {
  /****************************************************************************/
  /* READ COMMAND LINE ARGUMENTS                                              */
  /****************************************************************************/
  if (argc < 4 || argc > 5) {
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
    pool_size = atoi(argv[2]) * 1024;  // convert KB to B
  }  // end if (!atoi(argv[2]))

  /* open requests file for reading */
  req_file = fopen(argv[3], "r");

  /****************************************************************************/
  /* SETUP MEMORY POOL                                                        */
  /****************************************************************************/
  print_mem_config();

  mem_block_t init_block;
  init_block.id      = NOBODY;
  init_block.is_free = true;
  init_block.addr    = memory_pool;
  init_block.size    = BYTES_TO_WORDS(pool_size);
  init_block.prev    = NULL;
  memory_block_list  = list_pre(NULL, &init_block);
  init_block.curr    = memory_block_list;
  init_block.next    = NULL;

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
  
  history_list = list_pre(history_list, req_history);

  /****************************************************************************/
  /* LOAD AND PROCESS REQUESTS                                                */
  /****************************************************************************/
  int i;
  for (i = 0; argc == 5 ? i < atoi(argv[4]) : true; i++) {
    request_t * request = load_request(req_file);
    if (request == NULL) break;
    
    if (request->type == ALLOC) {
      mem_block_t * block = allocate_memory(request);

      /* Populate status entry */
      req_status_t stat;
      stat.req_id          = request->id;
      stat.req_type        = request->type;
      stat.req_size        = request->size;
      stat.req_granted     = block == NULL ? false : true;
      stat.req_addr        = stat.req_granted ? block->addr : NULL;
      stat.total_free      = total_free();
      stat.max_free        = max_free();
      stat.blocks_free     = blocks_free();
      stat.blocks_alloc    = blocks_alloc();
      req_history[i]       = stat;
      history_list = list_pre(history_list, req_history+i);
      if (!stat.req_granted) {
        char label[40];
        snprintf(label, 40, "ALLOCATION REQUEST %d FAILED", i-1);
        print_boxed(label, 40, 0);
        print_output(i, i);
        md_full();
      }
      
    } else {  // request type is FREE
      mem_block_t * block = free_memory(request);
      // assert(block != NULL);
      
      /* Populate status entry */
      req_status_t stat;
      stat.req_id          = request->id;
      stat.req_type        = request->type;
      stat.req_size        = block == NULL ? 0 : WORDS_TO_BYTES(block->size);
      stat.req_granted     = block == NULL ? false : true;
      stat.req_addr        = stat.req_granted ? block->addr : NULL;
      stat.total_free      = total_free();
      stat.max_free        = max_free();
      stat.blocks_free     = blocks_free();
      stat.blocks_alloc    = blocks_alloc();
      req_history[i]       = stat;
      history_list = list_pre(history_list, req_history+i);
    }

    /* Clean up */
    free(request);
    check_links();

    /* if ((i+1) % 20 == 0) { */
    /*   WAIT(); */
    /*   print_output(i-19, i); */
    /*   md_full(); */
    /* } */
    
    if (argc == 5) {
      print_output(i, i);
      md_full();
      WAIT();
      printf("\n\n\n\n\n\n\n");
    }
  }

  list_t * tmp = list_reverse(history_list);
  list_dispose(history_list);
  history_list = tmp;
  /****************************************************************************/
  /* OUTPUT                                                                   */
  /****************************************************************************/
  /* WAIT(); */
  /* print_output(0, i-1); */

  /* WAIT(); */
  /* md_full(); */
  
  int tg = total_granted();
  /* list_t * sh = size_history(); */
  // list_dump(sh);

  WAIT();
  print_failed();
  printf("total_granted = %d\n", tg);
  /****************************************************************************/
  /* CLEAN UP                                                                 */
  /****************************************************************************/
  list_dispose(memory_block_list);
  fclose(req_file);
  exit(EXIT_SUCCESS);
}


