#include "../lib/hash.h"

uint64_t hash(char * str) {
  uint64_t hash = 5381;
  char ch;

  while ((ch = (*str++)))
    hash = ((hash << 5) + hash) + ch;

  return hash;
}
