#include "lib/list.h"

#define MAX_POOL_SIZE (1048576)

int main(int argc, char *argv[]) {
  assert(argc == 4);
  char * policy_str = argv[1];
  size_t pool_size = atoi(argv[2]);
  char * req_file = argv[3];
  return 0;
}
