#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include "lib/user_input.h"
#include "lib/list.h"
#include "lib/hash.h"
#include "lib/util.h"

#define MIN(a, b) ((a) < (b) ? (a) : (b))

/* GLOBAL VARIABLES */
char countries[NUMC][BUFSIZ];
char alternate[NUMA][BUFSIZ];
char questions[NUMQ][BUFSIZ];
bool q_answers[NUMC][NUMQ];

int main(int argc, char * argv[]) {
  hash_table_t * hash_table;
  FILE *         ques_file;
  uint32_t       i, j, k;

  hash_table = load_alternates(HTSZ, alternate);

  while (1) {
    printf("Enter country name: ");
    char * str = lowercase(get_input_string());
    char * correct = match_str(str, hash_table, alternate);

    printf("closest match for %s: %s\n", str, correct);
  }

  return 0;
}

#undef MIN
