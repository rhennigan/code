// mem.c

#include <string.h>
#include <stdint.h>
#include "../lib/mem.h"

/******************************************************************************/
/* GLOBAL DEFINITIONS                                                         */
/******************************************************************************/
list_t *     memory_block_list = NULL;
void *       memory_pool[MAX_POOL_SIZE_WORDS];
req_status_t req_history[MAX_HISTORY_LENGTH];
list_t *     history_list = NULL;
policy_t     policy;
bytes_t      pool_size;
bytes_t      nb = 0;

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
static inline uint64_t void_to_num(void * v) { return (uint64_t)v; }
static inline int64_t offset_addr(void * a, void * base) {
  return void_to_num(a) - void_to_num(base);
}
int64_t rel_addr(void * a) {
  return a ? (int64_t)(void_to_num(a) - void_to_num(memory_pool)) : -1;
}

mem_block_t * block_from_list(list_t * list) {
  return list ? list_head(list) : NULL;
}

/******************************************************************************/
/* FREEING FUNCTIONS                                                          */
/******************************************************************************/
static bool match_ref(void * block_list, void * ref_addr) {
  int ref = *(int*)ref_addr;
  mem_block_t block = *(mem_block_t*)list_head(block_list);
  return ref == block.id;
}

// static void print_block(void * block_addr);

static bool match_addr(void * block_list, void * r_addr) {
  bytes_t base_addr = *(bytes_t *)r_addr;
  mem_block_t *block = (mem_block_t*)list_head(block_list);
  bytes_t block_addr = WORDS_TO_BYTES(offset_addr(block->addr, memory_pool));
  return base_addr == block_addr;
}

static inline bool is_right(mem_block_t * block) {
  return offset_addr(block->addr, memory_pool)/block->size % 2;
}

static inline bool can_merge(mem_block_t * block, list_t * list) {
  if (list == NULL || list_head(list) == NULL ||
      ((mem_block_t*)list_head(list)) == block ||
      !((mem_block_t*)list_head(list))->is_free) {
    return false;
  } else {
    mem_block_t * testb = list_head(list);
    bytes_t block_addr = WORDS_TO_BYTES(offset_addr(block->addr, memory_pool));
    bytes_t testb_addr = WORDS_TO_BYTES(offset_addr(testb->addr, memory_pool));
    bool block_right = block_addr / block->size % 2;
    bool testb_right = testb_addr / testb->size % 2;
    if (block_right && !testb_right) {
      return block_addr - block->size == testb_addr;
    } else if (!block_right && testb_right) {
      return block_addr + block->size == testb_addr;
    } else {
      return false;
    }
  }
}

/* static inline bool can_merge(mem_block_t * block, list_t * block_list) { */
/*   if (policy == BUDDY_SYSTEM) { */
/*     return can_merge_b(block, block_list); */
/*   } else { */
/*     return block_list != NULL */
/*         && list_head(block_list) != NULL */
/*         && ((mem_block_t*)list_head(block_list))->is_free; */
/*   } */
/* } */

static inline mem_block_t * merge_block(mem_block_t * curr_block) {
  assert(curr_block != NULL);
  assert(curr_block->is_free);

  list_t * prev_list = curr_block->prev;
  list_t * curr_list = curr_block->curr;
  list_t * next_list = curr_block->next;

  /* See if block can be merged right */
  if (can_merge(curr_block, next_list)) {
    mem_block_t * next_block = list_head(next_list);
    curr_block->size += next_block->size;            // 1

    list_t * new_next_list = next_block->next;
    curr_list->tail  = new_next_list;                // 2
    curr_block->next = new_next_list;                // 3

    if (new_next_list != NULL && list_head(new_next_list) != NULL) {
      mem_block_t * new_next_block = list_head(new_next_list);
      new_next_block->prev = curr_list;              // 4
    }

    free(next_block);                                // 5
    free(next_list);                                 // 6

    return merge_block(curr_block);
  }

  /* See if block can be merged left */
  if (can_merge(curr_block, prev_list)) {
    mem_block_t * prev_block = list_head(prev_list);
    prev_block->size += curr_block->size;            // 1

    list_t * new_next_list = curr_block->next;
    prev_list->tail  = new_next_list;                // 2
    prev_block->next = new_next_list;                // 3

    if (new_next_list != NULL && list_head(new_next_list) != NULL) {
      mem_block_t * new_next_block = list_head(new_next_list);
      new_next_block->prev = prev_list;              // 4
    }

    free(curr_block);                                // 5
    free(curr_list);                                 // 6

    return merge_block(prev_block);
  } else {
    return curr_block;
  }
}

mem_block_t * free_memory(request_t * request) {
  int ref = request->ref;
  list_t * curr_list_node = list_find(memory_block_list, &ref, &match_ref);
  if (curr_list_node == NULL || list_head(curr_list_node) == NULL) {
    return NULL;
  } else {
    mem_block_t * block = list_head(curr_list_node);
    block->is_free = true;
    return merge_block(block);
  }
}

/******************************************************************************/
/* ALLOCATION FUNCTIONS                                                       */
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

static mem_block_t * first_free(bytes_t size) {
  list_t * tmpr = list_filter(memory_block_list, &is_valid, &size);
  list_t * tmp = list_reverse(tmpr);
  list_dispose(tmpr);
  if (tmp == NULL) {
    return NULL;
  } else {
    return list_head(tmp);
  }
}  // end first_free

/******************************************************************************/
static bool smaller(void * a, void * b) {
  return (((mem_block_t*)a)->size < ((mem_block_t*)b)->size);
}

static mem_block_t * best_free(bytes_t size) {
  list_t * tmp = list_filter(memory_block_list, &is_valid, &size);
  tmp = list_extremum(tmp, &smaller);
  if (tmp == NULL) {
    return NULL;
  } else {
    return list_head(tmp);
  }
}

/******************************************************************************/
static bool larger(void * a, void * b) {
  return (((mem_block_t*)a)->size > ((mem_block_t*)b)->size);
}

/******************************************************************************/
static mem_block_t * split_block(mem_block_t * block, request_t * request) {
  if (block == NULL) return NULL;

  /* Block size */
  words_t req_words = BYTES_TO_WORDS(request->size);
  words_t req_size  = policy == BUDDY_SYSTEM ?
                        (block->size >> 1) >= req_words ?
                          block->size >> 1 :
                          block->size :
                        req_words;

  if (req_size == block->size) {
    block->id = request->id;
    block->is_free = false;
    return block;
  } else {

    /* Fill in new block information */
    mem_block_t * alloc_block = malloc(sizeof(mem_block_t));
    mem_block_t * rem_block   = malloc(sizeof(mem_block_t));
  
    alloc_block->id      = request->id;
    alloc_block->is_free = false;
    alloc_block->addr    = block->addr;
    alloc_block->size    = req_size;

    rem_block->id        = NOBODY;
    rem_block->is_free   = true;
    rem_block->addr      = (char*)block->addr + req_size;
    rem_block->size      = block->size - alloc_block->size;

    list_t * prev_list_node = block->prev;
    list_t * curr_list_node = block->curr;
    list_t * next_list_node = block->next;

    /**************** Update list pointers *************************************/
    /* (1, prev) -> (2, alloc) -> (3, rem) -> (4, next)                        */
    list_t *   rem_list_node = list_pre(next_list_node, rem_block);          // 3
    list_t * alloc_list_node = list_pre(rem_list_node, alloc_block);         // 2
  
    if (prev_list_node == NULL) {  // curr_list_node is full memory_block_list
      memory_block_list = alloc_list_node;
    } else {  // otherwise insert new blocks after the previous node
      prev_list_node->tail = alloc_list_node;                                // 1
    }

    /**************** Update block pointers ************************************/
    if (prev_list_node != NULL) {  // not at beginning of list
      mem_block_t * prev_block = (mem_block_t *)prev_list_node->head;        // 1
      prev_block->next = alloc_list_node;                                    // 1
    }

    alloc_block->prev =  prev_list_node;                                     // 2
    alloc_block->curr = alloc_list_node;                                     // 2
    alloc_block->next =   rem_list_node;                                     // 2

    rem_block->prev   = alloc_list_node;                                     // 3
    rem_block->curr   =   rem_list_node;                                     // 3
    rem_block->next   =  next_list_node;                                     // 3

    if (next_list_node != NULL) {                                            // 4
      mem_block_t * next_block = (mem_block_t *)next_list_node->head;        // 4
      next_block->prev = rem_list_node;                                      // 4
    }

    // rem_block = merge_block(rem_block);

    /***************************************************************************/
    free(curr_list_node);

    /* Might need to keep splitting if using buddy allocation */
    if (alloc_block->size >> 1 > req_words) {
      return split_block(alloc_block, request);
    } else {
      return alloc_block;
    }
  }
}

void fix_links() {
  list_t * prev = NULL;
  list_t * curr = memory_block_list;
  list_t * next = list_tail(curr);
  while (1) {
    mem_block_t * block = ((mem_block_t*)list_head(curr));
    block->prev = prev;
    block->curr = curr;
    block->next = next;
    if (next == NULL) break;
    prev = curr;
    curr = next;
    next = list_tail(next);
  }
}

/******************************************************************************/
/* static mem_block_t * buddy_split(request_t * request) { */
/*   assert(request != NULL); */
/*   bytes_t size = request->size; */
/*   list_t * tmp = list_filter(memory_block_list, &is_valid, &size); */
/*   if (tmp == NULL) { */
/*     return NULL; */
/*   } else { */
/*     mem_block_t * block = list_head(tmp); */
/*     words_t req_words = BYTES_TO_WORDS(size); */
/*     assert(block != NULL); */

/*     while ((req_words << 1) < block->size) {  // block can be split */
/*       bytes_t   s_bytes   = WORDS_TO_BYTES(block->size >> 1); */
/*       request_t split_req = { NOBODY, ALLOC, s_bytes, 0 }; */
/*       block = split_block(block, &split_req); */
/*       if (block != NULL) block->id = request->id; */
/*     } */
    
/*     return block; */
/*   } */
/* } */

mem_block_t * allocate_memory(request_t * request) {
  mem_block_t * target, * alloc_block = NULL;
  switch (policy) {
    case FIRST_FIT:
      target = first_free(request->size);
      alloc_block = split_block(target, request);
      break;
    case BEST_FIT:
      target = best_free(request->size);
      alloc_block = split_block(target, request);
      break;
    case BUDDY_SYSTEM:
      target = first_free(request->size);
      alloc_block = split_block(target, request);
      break;
  }
  return alloc_block;
}

static void * plus(void * x, void * y) {
  int sum = *(int*)x;
  bool ra = ((req_status_t*)y)->req_type == ALLOC;
  bool rg = ((req_status_t*)y)->req_granted;
  *(int*)x = ra && rg ? sum + 1 : sum;
  return x;
}

int total_granted() {
  int total = 0;
  return *(int*)list_foldl(history_list, &total, &plus) - 1;
}

static void * p_req_size(void * x, void * y) {
  list_t  * list = x;
  bytes_t * req_size;
  if (((req_status_t*)y)->req_addr != NULL) {
    req_size = &((req_status_t*)y)->req_size;
  } else {
    req_size = &nb;
  }
  list_t * node = list_pre(NULL, req_size);
  if (list != NULL)
    list->tail = node;
  return node;
}

list_t * size_history() {
  bytes_t * req_size = &((req_status_t*)list_head(history_list))->req_size;
  list_t * list = list_pre(NULL, req_size);
  list_foldl(list_tail(history_list), list, &p_req_size);
  list_t * r = list_reverse(list);
  list_dispose(list);
  return r;
}

/******************************************************************************/
/* FORMATTING AND OUTPUT                                                      */
/******************************************************************************/
words_t max_free() {
  words_t total = 0;
  list_t * free = list_filter(memory_block_list, &is_valid, &total);
  list_t * tmp = list_extremum(free, &larger);
  if (tmp == NULL) {  // no free blocks available
    // list_dispose(tmp)
    return 0;
  } else {
    mem_block_t * block = (mem_block_t*)list_head(tmp);
    // list_dispose(tmp)
    return block->size;
  }
}

words_t total_free() {
  words_t total = 0;
  list_t * free = list_filter(memory_block_list, &is_valid, &total);
  list_t * temp = free;
  while (temp != NULL) {
    total += ((mem_block_t*)list_head(temp))->size;
    temp = list_tail(temp);
  }
  // list_dispose(free);
  return total;
}

size_t blocks_free() {
  size_t count = 0;
  list_t * free = list_filter(memory_block_list, &is_valid, &count);
  count = list_length(free);
  // list_dispose(free);
  return count;
}

size_t blocks_alloc() {
  return list_length(memory_block_list) - blocks_free();
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
static const char * free_str = "\x1b[32mFREE\x1b[0m";
static const char * used_str = "\x1b[31mUSED\x1b[0m";
static const char * free_blk = "\x1b[32m\u258A\x1b[0m";
static const char * used_blk = "\x1b[31m\u258A\x1b[0m";
/* static const char * free_blk = "\x1b[32m\u2591\x1b[0m"; */

static void print_block(void * block_addr) {
  mem_block_t  block = *(mem_block_t*)block_addr;
  int          blid = block.id;
  const char * free = block.is_free ? free_str : used_str;
  char         side = is_right(&block) ? 'R' : 'L';
  void *       vadr = block.addr;
  int64_t      addr = WORDS_TO_BYTES(offset_addr(block.addr, memory_pool));
  void *       vrel = (void *)addr;
  bytes_t      size = WORDS_TO_BYTES(block.size);
  words_t      wrds = block.size;
  double       pcnt = 100.0 * (double)size / (double)pool_size;
  blid == 0 ? printf("       ") : printf("   %-4d", blid);
  printf("%7s", free);
  printf("%2c", side);
  printf("%12p", vadr);
  printf("%10p", vrel);
  printf("%7lu", addr);
  printf("%9luB", size);
  printf("%8luW", wrds);
  printf("%7.2f%%", pcnt);
  printf("\n");
}

static const int block_count = 64;
static void print_mem_gfx(void * block_addr) {
  mem_block_t  block = *(mem_block_t*)block_addr;
  bytes_t block_size = WORDS_TO_BYTES(block.size);
  bytes_t step_size  = pool_size / block_count;
  bytes_t base_addr  = WORDS_TO_BYTES(offset_addr(block.addr, memory_pool));
  bytes_t end_addr   = base_addr + block_size;
  size_t start_step  = base_addr / step_size;
  size_t end_step    = end_addr / step_size;
  const char * bchar = block.is_free ? free_blk : used_blk;
  for (size_t i = start_step; i < end_step; i++) printf("%s", bchar);
}

static inline void mem_bar_gfx() {
  printf("  %s", B_TL);
  for (int i = 0; i < block_count + 2; i++) printf("%s", B_HR);
  printf("%s\n  %s ", B_TR, B_VT);
  list_iter(memory_block_list, &print_mem_gfx);
  printf(" %s\n  %s", B_VT, B_BL);
  for (int i = 0; i < block_count + 2; i++) printf("%s", B_HR);
  printf("%s\n", B_BR);
}

void md_full() {
  char label[block_count + 2];
  size_t free  = blocks_free();
  size_t alloc = blocks_alloc();
  double avail = (double)WORDS_TO_BYTES(100*total_free()) / (double)pool_size;

  snprintf(label, sizeof(label),
           "CURRENT MEMORY: %lu used | %lu free | %.2f %% avail",
           alloc, free, avail);

  print_boxed(label, block_count + 4, 2);
  list_iter(memory_block_list, &print_block);
  mem_bar_gfx();
  printf("\n");
}

void md_free() {
  char label[66];
  size_t count = 0;
  list_t * fb  = list_filter(memory_block_list, &is_valid, &count);
  size_t free  = blocks_free();
  size_t alloc = blocks_alloc();
  double avail = (double)WORDS_TO_BYTES(100*total_free()) / (double)pool_size;

  snprintf(label, sizeof(label),
           "CURRENT MEMORY: %lu used | %lu free | %.2f %% avail",
           alloc, free, avail);

  printf("\n");
  print_boxed(label, 64, 0);
  list_iter(fb, &print_block);
  printf("\n");
}

static bool not_valid(void * block_addr, void * size_addr) {
  return !is_valid(block_addr, size_addr);
}

void md_alloc() {
  char label[66];
  size_t count = 0;
  list_t * ab  = list_filter(memory_block_list, &not_valid, &count);
  size_t free  = blocks_free();
  size_t alloc = blocks_alloc();
  double avail = (double)WORDS_TO_BYTES(100*total_free()) / (double)pool_size;

  snprintf(label, sizeof(label),
           "CURRENT MEMORY: %lu used | %lu free | %.2f %% avail",
           alloc, free, avail);

  printf("\n");
  print_boxed(label, 64, 0);
  list_iter(ab, &print_block);
  printf("\n");
}

void print_mem_config() {
  printf("\n\n\n\n");
  print_boxed("MEMORY CONFIG", 40, 0);
  printf(" MAX_POOL_SIZE_KBYTES = %lu\n", MAX_POOL_SIZE_KBYTES);
  printf(" MIN_ALLOC_BYTES      = %lu\n", MIN_ALLOC_BYTES);
  printf(" MAX_HISTORY_LENGTH   = %lu\n", MAX_HISTORY_LENGTH);
  printf("                           \n");
  printf(" MAX_POOL_SIZE_BYTES  = %lu\n", MAX_POOL_SIZE_BYTES);
  printf(" WORD_SIZE_BYTES      = %lu\n", WORD_SIZE_BYTES);
  printf(" MAX_POOL_SIZE_WORDS  = %lu\n", MAX_POOL_SIZE_WORDS);
  printf(" MIN_ALLOC_WORDS      = %lu\n", MIN_ALLOC_WORDS);
  printf("\n\n\n\n");
}

static inline void print_row(int row) {
  int     sn = req_history[row].req_id;
  bytes_t sz = req_history[row].req_size;
  /* int64_t ad = offset_addr(req_history[row].req_addr, memory_pool) * */
  /*              WORD_SIZE_BYTES; */
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
  printf("%1s %7lu B %s", " ", tf, B_VT);
  printf("%1s %9lu B %s", " ", lp, B_VT);
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
  if (pool_size >= 1048576) {
    snprintf(s, 80, "%4.2f MB", (double)pool_size / (double)1048576);
  } else if (pool_size >= 1024) {
    snprintf(s, 80, "%4.2f KB", (double)pool_size / (double)1024);
  } else {  // no unit conversion
    snprintf(s, 80, "%lu B", pool_size);
  }  // end if (pool_size > 1048576)

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

static void print_failed_aux(void * x) {
  req_status_t * stat = (req_status_t*)x;
  bool ra = stat->req_type == ALLOC;
  bool rg = stat->req_granted;
  if (ra && !rg) {
    int req_id = stat->req_id;
    bytes_t req_size = stat->req_size;
    printf("Failed Req %d is size %lu\n", req_id, req_size);
  }
}

void print_failed() {
  list_iter(history_list, &print_failed_aux);
}

static void print_size(void * x) {
  printf("%lu ", *(bytes_t*)x);
}

void print_sizes(list_t * sh) {
  list_iter(sh, &print_size);
}
