#include "../lib/hash.h"

uint64_t hash(uint8_t * str) {
  uint64_t hash = 5381;
  int32_t  ch;
  while ((ch = (*str++)))
    hash = ((hash << 5) + hash) + ch;
  return hash;
}
