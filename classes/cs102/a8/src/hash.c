#include "../lib/hash.h"

uint64_t hash(char * str) {
  uint64_t hash = 5381;
  char ch;

  while ((ch = (*str++)))
    hash = ((hash << 5) + hash) + ch;

  return hash;
}

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MIN3(a, b, c) MIN(MIN(a, b), c)

int levenshtein(char *s1, char *s2) {
  uint32_t s1len, s2len, x, y, ld, od;
  s1len = strlen(s1);
  s2len = strlen(s2);
  uint32_t c[s1len+1];
  for (y = 1; y <= s1len; y++)
    c[y] = y;
  for (x = 1; x <= s2len; x++) {
    c[0] = x;
    for (y = 1, ld = x-1; y <= s1len; y++) {
      od = c[y];
      c[y] = MIN3(c[y] + 1, c[y-1] + 1, ld + (s1[y-1] == s2[x-1] ? 0 : 1));
      ld = od;
    }
  }
  return(c[s1len]);
}
