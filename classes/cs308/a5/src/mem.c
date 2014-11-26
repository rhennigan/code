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
    char * size_str = strtok_r(NULL,   " \n", &saveptr);
    char * ref_str  = strtok_r(NULL,   " \n", &saveptr);

    printf("id_str   = %s\n", id_str);
    printf("type_str = %s\n", type_str);
    printf("size_str = %s\n", size_str);
    printf("ref_str  = %s\n", ref_str);

    return NULL;
  }
}

/******************************************************************************/
mem_block_t * first_free(bytes_t size) {
  list_t * tmp = memory_block_list;
  words_t w_sz = BYTES_TO_WORDS(size);
  while (tmp != NULL) {
    mem_block_t * block = (mem_block_t*)list_head(tmp);
    if (block->is_free && (block->size > w_sz)) {
      return block;
    } else {  // not free, keep looking
      tmp = list_tail(tmp);
    }  // end if (block->is_free && (block->size > min_size))
  }  // end while (tmp != NULL)
  return NULL;
}  // end first_free



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
