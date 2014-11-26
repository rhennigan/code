// mem.c

#include <string.h>
#include "../lib/mem.h"

/******************************************************************************/
/* GLOBAL DEFINITIONS                                                         */
/******************************************************************************/
list_t *     memory_block_list = NULL;
void *       memory_pool[MAX_POOL_SIZE_WORDS];
req_status_t req_history[MAX_HISTORY_LENGTH];
policy_t     policy;
bytes_t      pool_size;

const char * policy_names[] = {
  [FIRST_FIT]    = "FIRST_FIT",
  [BEST_FIT]     = "BEST_FIT",
  [BUDDY_SYSTEM] = "BUDDY_SYSTEM"
};

const char * req_type_names[] = {
  [ALLOC] = "ALLOC",
  [FREE]  = "FREE",
  [NONE]  = "NONE"
};

char cols[6][80] = {
  "SERIAL-NUM",
  "REQUEST",
  "SIZE",
  "ALLOC-ADDR",
  "TOTAL-FREE",
  "LARGEST-PART"
};

/******************************************************************************/
request_t * load_request(FILE * file) {
  char buffer[80];
  if (fgets(buffer, 80, file) == NULL) {
    return NULL;
  } else {
    char * saveptr;
    char * id_str   = strtok_r(buffer, " \n", &saveptr);
    char * type_str = strtok_r(NULL,   " \n", &saveptr);
    char * ref_str  = strtok_r(NULL,   " \n", &saveptr);

    request_t * request = malloc(sizeof(request_t));
    request->id   = atoi(id_str);
    request->type = strcmp(type_str, "alloc") == 0 ? ALLOC : FREE;
    request->size = atoi(ref_str);
    request->ref  = atoi(ref_str);

    return request;
  }
}

/******************************************************************************/
static bool is_valid(void * block_addr, void * size_addr) {
  if (block_addr == NULL || !((mem_block_t*)block_addr)->is_free) {
    return false;
  } else {  // block is free, check size
    bytes_t block_size = WORDS_TO_BYTES(((mem_block_t*)block_addr)->size);
    bytes_t req_size   = *((bytes_t*)size_addr);
    return block_size > req_size;
  }  // end if (block_addr == NULL || !((mem_block_t*)block_addr)->is_free)
}  // end is_valid

mem_block_t * first_free(bytes_t size) {
  list_t * tmp = list_filter(memory_block_list, &is_valid, &size);
  if (tmp == NULL) {
    return NULL;
  } else {
    return list_head(tmp);
  }
}  // end first_free

static bool smaller(void * a, void * b) {
  return (((mem_block_t*)a)->size < ((mem_block_t*)b)->size);
}

mem_block_t * best_free(bytes_t size) {
  list_t * tmp = list_filter(memory_block_list, &is_valid, &size);
  tmp = list_extremum(tmp, &smaller);
  if (tmp == NULL) {
    return NULL;
  } else {
    return list_head(tmp);
  }
}

void split_block(mem_block_t * block, request_t * request) {
  list_t * prev_list_node = block->prev;
  list_t * curr_list_node = block->curr;
  list_t * next_list_node = block->next;

  mem_block_t * alloc_block = malloc(sizeof(mem_block_t));
  mem_block_t * rem_block   = malloc(sizeof(mem_block_t));

  /* Fill in new block information */
  alloc_block->id      = request->id;
  alloc_block->is_free = false;
  alloc_block->addr    = block->addr;
  alloc_block->size    = BYTES_TO_WORDS(request->size);

  rem_block->id        = NOBODY;
  rem_block->is_free   = true;
  rem_block->addr      = (char*)block->addr + request->size;
  rem_block->size      = block->size - alloc_block->size;

  /**************** Update list pointers ****************/
  /* (1, prev) -> (2, alloc) -> (3, rem) -> (4, next)   */
  list_t *   rem_list_node = list_pre(next_list_node, rem_block);  // 3
  list_t * alloc_list_node = list_pre(rem_list_node, alloc_block); // 2
  
  if (prev_list_node == NULL) {  // curr_list_node is full memory_block_list
    memory_block_list = alloc_list_node;
  } else {  // otherwise insert new blocks after the previous node
    prev_list_node->tail = alloc_list_node;                        // 1
  }

  /************ Update block pointers ************/
  if (prev_list_node != NULL) {
    mem_block_t * prev_block = (mem_block_t *)prev_list_node->head;
    prev_block->next = alloc_list_node;
  }

  alloc_block->prev    = block->prev;
  // TODO: need to update memory_block_list and alloc_block->current ptr

  
  // rem_block->prev      = alloc_block->curr;
  rem_block->curr      = list_pre(block->next, rem_block);
  rem_block->next      = block->next;
}

void * allocate_memory(request_t * request) {
  mem_block_t * target = NULL;
  switch (policy) {
    case FIRST_FIT:
      target = first_free(request->size);
      break;
    case BEST_FIT:
      target = best_free(request->size);
      break;
    case BUDDY_SYSTEM:
      printf("not yet implemented\n");
      exit(EXIT_FAILURE);  // TODO: implement buddy system split func
      break;
  }
  return target;
}


/******************************************************************************/
/* FORMATTING AND OUTPUT                                                      */
/******************************************************************************/
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
  print_boxed("MEMORY CONFIG", 40, 0);
  printf(" MAX_POOL_SIZE_KBYTES = %lu\n", MAX_POOL_SIZE_KBYTES);
  printf(" MIN_ALLOC_BYTES      = %lu\n", MIN_ALLOC_BYTES);
  printf(" MAX_HISTORY_LENGTH   = %lu\n", MAX_HISTORY_LENGTH);
  printf("                           \n");
  printf(" MAX_POOL_SIZE_BYTES  = %lu\n", MAX_POOL_SIZE_BYTES);
  printf(" WORD_SIZE_BYTES      = %lu\n", WORD_SIZE_BYTES);
  printf(" MAX_POOL_SIZE_WORDS  = %lu\n", MAX_POOL_SIZE_WORDS);
  printf(" MIN_ALLOC_WORDS      = %lu\n", MIN_ALLOC_WORDS);
}

static inline void print_row(int row) {
  int     sn = req_history[row].req_id;
  bytes_t sz = req_history[row].req_size;
  void *  ad = req_history[row].req_addr;
  bytes_t tf = WORDS_TO_BYTES(req_history[row].total_free);
  bytes_t lp = WORDS_TO_BYTES(req_history[row].max_free);
  char    rq[6];
  switch (req_history[row].req_type) {
    case ALLOC:
      snprintf(rq, 6, "alloc");
      break;
    case FREE:
      snprintf(rq, 5, "free");
      break;
    case NONE:
      snprintf(rq, 5, "init");
      break;
  }
  printf("%s", B_VT);
  printf("%1s %-9d %s",   " ", sn, B_VT);
  printf("%1s %-6s %s",   " ", rq, B_VT);
  printf("%1s %9lu B %s", " ", sz, B_VT);
  printf("%1s %-9p %s",   " ", ad, B_VT);
  printf("%1s %7lu K %s", " ", tf, B_VT);
  printf("%1s %9lu K %s", " ", lp, B_VT);
  printf("\n");
}

void print_output(int from, int to) {
  char p[80];
  switch (policy) {
    case FIRST_FIT:
      snprintf(p, 80, "First Fit");
      break;
    case BEST_FIT:
      snprintf(p, 80, "Best Fit");
      break;
    case BUDDY_SYSTEM:
      snprintf(p, 80, "Buddy System");
      break;
  }  // end switch (policy)

  char s[80];
  if (pool_size > 1023) {
    snprintf(s, 80, "%4.2f MB", (double)pool_size / (double)1024);
  } else {  // no unit conversion
    snprintf(s, 80, "%lu KB", pool_size);
  }  // end if (pool_size > 1048575)

  /* Top bar */
  printf("\n%s", B_TL);
  for (int i = 0; i < 78; i++)
    printf("%s", B_HR);
  printf("%s\n", B_TR);

  /* Header label */
  printf("%s", B_VT);
  printf("     MANAGEMENT POLICY = %-12s   ", p);
  printf("     POOL SIZE = %-10s      ", s);
  printf("     %s\n", B_VT);

  /* Separator between header and column labels */
  printf("%s", B_LM);
  for (int i = 0; i < 6; i++) {
    for (size_t j = 0; j < (i == 2 ? 14 : strlen(cols[i])+2); j++)
      printf("%s", B_HR);
    if (i == 5) break;
    printf("%s", B_TM);
  }
  printf("%s\n", B_RM);

  /* Column labels */
  printf("%s", B_VT);
  for (int i = 0; i < 6; i++)
    printf(i == 2 ? " %12s %s" : " %s %s" , cols[i], B_VT);
  printf("\n");

  /* Bottom of column labels */
  printf("%s", B_LM);
  for (int i = 0; i < 6; i++) {
    for (size_t j = 0; j < (i == 2 ? 14 : strlen(cols[i])+2); j++)
      printf("%s", B_HR);
    if (i == 5) break;
    printf("%s", B_CM);
  }
  printf("%s\n", B_RM);

  /* Print each row */
  for (int i = from; i <= to; i++) {
    print_row(i);
  }

  /* Bottom of output table */
  printf("%s", B_BL);
  for (int i = 0; i < 6; i++) {
    for (size_t j = 0; j < (i == 2 ? 14 : strlen(cols[i])+2); j++)
      printf("%s", B_HR);
    if (i == 5) break;
    printf("%s", B_BM);
  }
  printf("%s\n", B_BR);
}
