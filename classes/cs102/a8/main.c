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
char    countries[NUMC][BUFSIZ];
char    alternate[NUMA][BUFSIZ];
char    questions[NUMQ][BUFSIZ];
int32_t q_answers[NUMC][NUMQ+1];

int main(int argc, char * argv[]) {
  hash_table_t * hash_table;

  load_text("data/countries.csv", NUMC, countries);
  load_text("data/questions.csv", NUMQ, questions);
  hash_table = load_alts("data/alternates.csv", HTSZ, alternate);
  load_answ("data/answers.csv", NUMQ, q_answers);

  for (uint32_t i = 0; i < NUMC; i++) {
    printf("%d ", q_answers[i][0]);
    for (uint32_t j = 1; j < NUMQ+1; j++) {
      printf("%d", q_answers[i][j]);
    }
    printf("\n");
  }

  bintree_t * bt = bt_init();
  list_t * cvecs = NULL;
  for (int32_t i = NUMC-1; i >= 0; i--) {
    cvecs = list_cons(cvecs, q_answers[i]);
  }
  bt->data = cvecs;

  printf("\n\n");

  div_tree(bt);

  printf("depth = %lu\n", bt_depth(bt));

  printf("\n-----------------------\n");
  list_t * tmp = bt_get_data(bt);
  while (tmp != NULL) {
    void * addr = list_head(tmp);
    int32_t * cvec = (int32_t*)addr;
    printf("%s, ", countries[cvec[0]]);
    tmp = list_tail(tmp);
  }
  printf("\n-----------------------\n");

  int32_t ques_num = split_by(bt_get_data(bt));
  char * question = questions[ques_num];
  while (1) {
    printf("%s (yes/no): ", question);
    char * ans = get_input_string();
    if (strcmp(ans, "yes") == 0) {
      bt = bt_get_left(bt);
      break;
    } else if (strcmp(ans, "no") == 0) {
      bt = bt_get_right(bt);
      break;
    } else {
      printf("invalid input, please respond with \"yes\" or \"no\"\n");
    }
  }

  /* list_t * cvecs0 = bt_get_data(bt); */
  /* int32_t split0 = split_by(cvecs0); */
  /* char * initq = questions[split0]; */
  /* printf("initq = %s\n", initq); */

  /* bintree_t * btl = bt_get_left(bt); */
  /* bintree_t * btr = bt_get_right(bt); */

  /* list_t * cvecsl = bt_get_data(btl); */
  /* list_t * cvecsr = bt_get_data(btr); */

  /* printf("\n-----------------------\n"); */
  /* while (cvecsl != NULL) { */
  /*   void * addr = list_head(cvecsl); */
  /*   int32_t * cvec = (int32_t*)addr; */
  /*   printf("%s, ", countries[cvec[0]]); */
  /*   cvecsl = list_tail(cvecsl); */
  /* } */

  /* printf("\n-----------------------\n"); */
  /* while (cvecsr != NULL) { */
  /*   void * addr = list_head(cvecsr); */
  /*   int32_t * cvec = (int32_t*)addr; */
  /*   printf("%s, ", countries[cvec[0]]); */
  /*   cvecsr = list_tail(cvecsr); */
  /* } */
  /* for (uint32_t i = 0; i < NUMC; i++) */
  /*   printf("%s\n", countries[i]); */

  /* for (uint32_t i = 0; i < NUMQ; i++) */
  /*   printf("%s\n", questions[i]); */



  /* printf("Enter country name: "); */
  /* char * str = lowercase(get_input_string()); */
  /* char * correct = match_str(str, hash_table, alternate); */

  return 0;
}

#undef MIN
