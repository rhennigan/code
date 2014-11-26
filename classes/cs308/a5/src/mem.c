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
#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MAX(a, b) ((a) > (b) ? (a) : (b))

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
  print_boxed("MEM_CONFIG", 35, 0);
  printf(" MAX_POOL_SIZE_KBYTES = %lu\n", MAX_POOL_SIZE_KBYTES);
  printf(" MIN_ALLOC_BYTES      = %lu\n", MIN_ALLOC_BYTES);
  printf(" MAX_HISTORY_LENGTH   = %lu\n", MAX_HISTORY_LENGTH);
  printf("                           \n");
  printf(" MAX_POOL_SIZE_BYTES  = %lu\n", MAX_POOL_SIZE_BYTES);
  printf(" WORD_SIZE_BYTES      = %lu\n", WORD_SIZE_BYTES);
  printf(" MAX_POOL_SIZE_WORDS  = %lu\n", MAX_POOL_SIZE_WORDS);
  printf(" MIN_ALLOC_WORDS      = %lu\n", MIN_ALLOC_WORDS);
}

void print_output_header() {
  /* char label[80]; */
  /* char * mp = "MANAGEMENT POLICY"; */
  /* char * ps = "POOL SIZE"; */
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
  /* size_t s = pool_size; */
  /* snprintf(label, 80, "%s = %s          %s = %lu KB", mp, p, ps, s); */
  /* print_boxed(label, 80, 0); */

  /* Top bar */
  printf("%s", B_TL);
  for (int i = 0; i < 78; i++)
    printf("%s", B_HR);
  printf("%s\n", B_TR);

  /* Header label */
  printf("%s", B_VT);
  printf("    MANAGEMENT POLICY = %s", p);
  printf("    POOL SIZE = %lu KB", pool_size);
  printf("%s\n", B_VT);

  char cols[6][80] = {
    "SERIAL-NUM",
    "REQUEST",
    "SIZE    ",
    "ALLOC-ADDR  ",
    "TOTAL-FREE  ",
    "LARGEST-PART"
  };
  printf("%s", B_LM);
  for (int i = 0; i < 6; i++) {
    for (size_t j = 0; j < strlen(cols[i])+2; j++)
      printf(" ");
    printf("%s", B_TM);
  }
  printf("%s\n", B_RM);

  printf("%s", B_VT);
  for (int i = 0; i < 6; i++)
    printf(" %s %s", cols[i], B_VT);
}
