#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <limits.h>
#include "lib/user_input.h"
#include "lib/list.h"
#include "lib/hash.h"
#include "lib/util.h"
#include "lib/bintree.h"

/* GLOBAL VARIABLES */
char countries[NUMC][BUFSIZ];
char alternate[NUMA][BUFSIZ];
char questions[NUMQ][BUFSIZ];
bool q_answers[NUMC][NUMQ];

int main(int argc, char * argv[]) {
  hash_table_t * hash_table;

  load_text("data/countries.csv", NUMC, countries);
  load_text("data/questions.csv", NUMQ, questions);
  hash_table = load_alts("data/alternates.csv", HTSZ, alternate);
  load_answ("data/answers.csv", NUMQ, q_answers);

  bintree_t * bt = bt_init();
  list_t * cvecs = NULL;
  for (int32_t i = NUMC-1; i >= 0; i--) {
    
  }
  /* for (uint32_t i = 0; i < NUMC; i++) */
  /*   printf("%s\n", countries[i]); */

  /* for (uint32_t i = 0; i < NUMQ; i++) */
  /*   printf("%s\n", questions[i]); */

  /* for (uint32_t i = 0; i < NUMC; i++) { */
  /*   for (uint32_t j = 0; j < NUMQ; j++) { */
  /*     printf("%c", q_answers[i][j] ? 'T' : 'F'); */
  /*   } */
  /*   printf("\n"); */
  /* } */

  /* printf("Enter country name: "); */
  /* char * str = lowercase(get_input_string()); */
  /* char * correct = match_str(str, hash_table, alternate); */

  return 0;
}

#undef MIN
