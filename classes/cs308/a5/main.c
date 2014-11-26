#include <string.h>
#include "lib/list.h"

#define MAX_POOL_SIZE (1048576)
#define MIN_ALLOC (32)

typedef enum { FIRST_FIT, BEST_FIT, BUDDY_SYSTEM } policy_t;

void print_usage(char * name);

int main(int argc, char *argv[]) {
  /****************************************************************************/
  /* READ COMMAND LINE ARGUMENTS                                              */
  /****************************************************************************/
  if (argc != 4) {
    print_usage(argv[0]);
    exit(EXIT_FAILURE);
  }

  policy_t policy;
  size_t pool_size;
  char * req_file;

  if (strcmp(argv[1], "first") == 0) {
    policy = FIRST_FIT;
  } else if (strcmp(argv[1], "best") == 0) {
    policy = BEST_FIT;
  } else if (strcmp(argv[1], "buddy") == 0) {
    policy = BUDDY_SYSTEM;
  } else {
    print_usage(argv[0]);
    exit(EXIT_FAILURE);
  }

  if (!atoi(argv[2])) {
    printf("error: the pool size must be a positive integer\n");
    exit(EXIT_FAILURE);
  } else {
    pool_size = atoi(argv[2]);
  }

  req_file = argv[3];

  /****************************************************************************/
  /* SETUP MEMORY POOL                                                        */
  /****************************************************************************/

  return 0;
}

void print_usage(char * name) {
  printf("error reading arguments\n");
  printf("usage:\n");
  printf("%s ", name);
  printf("[policy:(first|best|buddy)] ");
  printf("[pool_size:int] ");
  printf("[req_file:string]\n");
}
