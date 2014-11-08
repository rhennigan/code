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

void get_help(hash_table_t * hash_table);
void hline();

int main(int argc, char * argv[]) {
  hash_table_t * hash_table;
  FILE * graph_file = fopen("data/graph_data.csv", "w");

  load_text("data/countries.csv", NUMC, countries);
  load_text("data/questions.csv", NUMQ, questions);
  hash_table = load_alts("data/alternates.csv", HTSZ, alternate);
  load_answ("data/answers.csv", NUMQ, q_answers);

  bintree_t * bt = bt_init();
  list_t * cvecs = NULL;
  for (int32_t i = NUMC-1; i >= 0; i--) {
    cvecs = list_cons(cvecs, q_answers[i]);
  }

  bt->data = cvecs;

  printf("Building an optimal decision tree...\n");
  div_tree(bt, graph_file);
  hline();
  printf("Decision tree stats:\n");
  printf("  depth = %lu\n", bt_depth(bt));
  printf("  leaves = %lu\n", bt_leaf_count(bt));
  printf("  nodes = %lu\n", bt_node_count(bt));

  hline();
  printf("Welcome to the country guessing game!\n");
  printf("I know %d facts for each of the %d countries\n", NUMQ, NUMC);
  printf("Pick a country and I'll ask you a series of yes/no questions");
  printf(" about that country\nand I'll try to guess the correct one");
  printf(" as soon as possible.\n");
  hline();

  uint32_t q_asked = 0;
  while (1) {
    if (bt_is_leaf(bt)) {
      list_t * cvecs = bt_get_data(bt);
      if (list_length(cvecs) == 1) {
        printf("I found the answer with %d questions: ", q_asked);
      } else {
        printf("I've run out of questions to ask.");
        printf("I've narrowed the choice down to the following:\n");
      }
      while (cvecs != NULL) {
        void * addr = list_head(cvecs);
        int32_t * cvec = (int32_t*)addr;
        char * country = countries[cvec[0]];
        printf("%s\n", country);
        cvecs = list_tail(cvecs);
      }
      bt_dispose(bt);
      exit(EXIT_SUCCESS);
    }
    int32_t ques_num = split_by(bt_get_data(bt));
    char * question = questions[ques_num];
    while (1) {
      printf("\n%lu countries remaining...\n", list_length(bt_get_data(bt)));
      printf("%s (yes/no/unknown): ", question);
      char * ans = get_input_string();
      if (strcmp(ans, "unknown") == 0) {
        get_help(hash_table);
      } else if (strcmp(ans, "yes") == 0) {
        bt = bt_get_left(bt);
        q_asked++;
        break;
      } else if (strcmp(ans, "no") == 0) {
        bt = bt_get_right(bt);
        q_asked++;
        break;
      } else {
        printf("invalid input, please respond with \"yes\" or \"no\"\n");
      }
    }
  }

  return 0;
}

void get_help(hash_table_t * ht) {
  printf("\n\n");
  printf("If you are not sure of an answer, you can check the database ");
  printf("for any country.\n");
  printf("Enter a country name to retrieve data: ");
  char * str = get_input_string();
  int32_t cfv;
  char * mst = match(lowercase(str), ht, alternate, &cfv);
  if (cfv < 100) {
    printf("\nInterpreting %s as %s (confidence: %d%%)\n\n", str, mst, cfv);
    WAIT();
  }
  int32_t page = 1;
  printf("\n\n");
  printf("%s Facts (page %d)\n", mst, page);
  hline();
  int32_t cidx = -1;
  for (int32_t i = 0; i < NUMC; i++) {
    if (strcmp(countries[i], mst) == 0) {
      cidx = i;
    }
  }
  assert(cidx >= 0);
  for (int32_t i = 0; i < NUMQ; i++) {
    char * q = questions[i];
    char * a = q_answers[cidx][i+1] ? "YES" : "NO";
    printf("%s = %s\n", q, a);
    if (i % 20 == 19) {
      hline();
      WAIT();
      page++;
      printf("%s Facts (page %d)\n", mst, page);
      hline();
    }
  }
  hline();
  printf("\n\n");
}

void hline() {
  for (uint32_t i = 0; i < 80; i++) printf("-");
  printf("\n");
}

#undef MIN
