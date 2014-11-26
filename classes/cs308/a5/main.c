#include <string.h>
#include "lib/list.h"

#define MAX_POOL_SIZE (1048576)
#define MIN_ALLOC (32)

typedef enum { FIRST_FIT, BEST_FIT, BUDDY_SYSTEM } policy_t;

int main(int argc, char *argv[]) {
/******************************************************************************/
/* READ COMMAND LINE ARGUMENTS                                                */
/******************************************************************************/
  assert(argc == 4);
  policy_t policy;
  if (strcmp(argv[1], "first") == 0) {
    policy = FIRST_FIT;
  } else if (strcmp(argv[1], "best") == 0) {
    policy = BEST_FIT;
  } else if (strcmp(argv[1], "buddy") == 0) {
    policy = BUDDY_SYSTEM;
  } else {
    printf("error reading arguments\n");
    printf("usage:\n");
    printf("%s ", argv[0]);
    printf("[policy : first|best|buddy] ");
    printf("[pool_size : int] ");
    printf("[req_file : string]\n");
    exit(EXIT_FAILURE);
  }
  size_t pool_size = atoi(argv[2]);
  char * req_file = argv[3];
  return 0;
}
