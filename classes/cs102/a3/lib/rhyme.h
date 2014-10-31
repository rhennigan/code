#define _CRT_SECURE_NO_WARNINGS


#include <string.h>
#include <ctype.h>
#include "data/linked_list.h"
#include "user_input.h"

def_list_full(int, "%d");

typedef struct {
  char * symbol;
  int code;
} conv_key;



conv_key key_table[] = 
{
  (conv_key) {  "AA",  0 },
  (conv_key) { "AA0",  1 },
  (conv_key) { "AA1",  2 },
  (conv_key) { "AA2",  3 },
  (conv_key) {  "AE",  4 },
  (conv_key) { "AE0",  5 },
  (conv_key) { "AE1",  6 },
  (conv_key) { "AE2",  7 },
  (conv_key) {  "AH",  8 },
  (conv_key) { "AH0",  9 },
  (conv_key) { "AH1", 10 },
  (conv_key) { "AH2", 11 },
  (conv_key) {  "AO", 12 },
  (conv_key) { "AO0", 13 },
  (conv_key) { "AO1", 14 },
  (conv_key) { "AO2", 15 },
  (conv_key) {  "AW", 16 },
  (conv_key) { "AW0", 17 },
  (conv_key) { "AW1", 18 },
  (conv_key) { "AW2", 19 },
  (conv_key) {  "AY", 20 },
  (conv_key) { "AY0", 21 },
  (conv_key) { "AY1", 22 },
  (conv_key) { "AY2", 23 },
  (conv_key) {   "B", 24 },
  (conv_key) {  "CH", 25 },
  (conv_key) {   "D", 26 },
  (conv_key) {  "DH", 27 },
  (conv_key) {  "EH", 28 },
  (conv_key) { "EH0", 29 },
  (conv_key) { "EH1", 30 },
  (conv_key) { "EH2", 31 },
  (conv_key) {  "ER", 32 },
  (conv_key) { "ER0", 33 },
  (conv_key) { "ER1", 34 },
  (conv_key) { "ER2", 35 },
  (conv_key) {  "EY", 36 },
  (conv_key) { "EY0", 37 },
  (conv_key) { "EY1", 38 },
  (conv_key) { "EY2", 39 },
  (conv_key) {   "F", 40 },
  (conv_key) {   "G", 41 },
  (conv_key) {  "HH", 42 },
  (conv_key) {  "IH", 43 },
  (conv_key) { "IH0", 44 },
  (conv_key) { "IH1", 45 },
  (conv_key) { "IH2", 46 },
  (conv_key) {  "IY", 47 },
  (conv_key) { "IY0", 48 },
  (conv_key) { "IY1", 49 },
  (conv_key) { "IY2", 50 },
  (conv_key) {  "JH", 51 },
  (conv_key) {   "K", 52 },
  (conv_key) {   "L", 53 },
  (conv_key) {   "M", 54 },
  (conv_key) {   "N", 55 },
  (conv_key) {  "NG", 56 },
  (conv_key) {  "OW", 57 },
  (conv_key) { "OW0", 58 },
  (conv_key) { "OW1", 59 },
  (conv_key) { "OW2", 60 },
  (conv_key) {  "OY", 61 },
  (conv_key) { "OY0", 62 },
  (conv_key) { "OY1", 63 },
  (conv_key) { "OY2", 64 },
  (conv_key) {   "P", 65 },
  (conv_key) {   "R", 66 },
  (conv_key) {   "S", 67 },
  (conv_key) {  "SH", 68 },
  (conv_key) {   "T", 69 },
  (conv_key) {  "TH", 70 },
  (conv_key) {  "UH", 71 },
  (conv_key) { "UH0", 72 },
  (conv_key) { "UH1", 73 },
  (conv_key) { "UH2", 74 },
  (conv_key) {  "UW", 75 },
  (conv_key) { "UW0", 76 },
  (conv_key) { "UW1", 77 },
  (conv_key) { "UW2", 78 },
  (conv_key) {   "V", 79 },
  (conv_key) {   "W", 80 },
  (conv_key) {   "Y", 81 },
  (conv_key) {   "Z", 82 },
  (conv_key) {  "ZH", 83 }
};


int
convert_key(char * symbol)
{
  int i;
  for (i = 0; i < 84; i++)
  {
    if (strcmp(symbol, key_table[i].symbol) == 0)
    {
      return key_table[i].code;
    }
  }

  printf("key lookup failed\n");
  exit(EXIT_FAILURE);
}

bool
valid_ch (char ch)
{
  return (isalpha(ch) || ch == ' ');
}



typedef struct {
  char word[BUFSIZ];
  int_list_t * code;
} p_key;


void
print_key(p_key * key)
{
  printf("key: word = %s, code = ", key->word);
  int_list_print(key->code);
}


p_key *
load_key (FILE * file)
{
  char buffer[BUFSIZ];
  char word[BUFSIZ];
  char * sym = malloc(BUFSIZ);
  const char split[BUFSIZ] = " \n";

  p_key * key = (p_key *) malloc (sizeof (p_key));
  assert(key);
  
  do
  {
    if(fgets(buffer, BUFSIZ, file) == NULL)
    {
      return NULL;
    }
  }
  while (buffer[0] == ';');

  
  char * token = strtok(buffer, split); 
  strcpy(word, lowercase(token));
  unsigned int i;
  for (i = 0; i < strlen(word); i++)
    {
      if (!valid_ch(word[i]))
        {
          word[i] = '\0';
        }
    }
  
  /* key->word = (char *)malloc(BUFSIZ); */
  /* assert(key->word); */
  
  strcpy(key->word, word);
  key->code = NULL;

  sym = strtok(NULL, split);
  
  while (sym != NULL)
    {
      key->code = int_list_cons(key->code, convert_key(sym));
      sym = strtok(NULL, split);
    }
    
  return key;
}



int
load_all_keys(const char * path, p_key * p_data[])
{
  FILE * file = fopen(path, "r");
  p_key * key;

  int i = 0;
  key = load_key(file);
  while (key != NULL)
    {
      p_data[i++] = key;
      key = load_key(file);
    }

  fclose(file);

  return i; // number of keys loaded
}


typedef struct {
  int points;
  char * player_name;
  p_key * key;
} _rhyme_t;

typedef _rhyme_t (*rhyme_t);

def_list_base(rhyme_t);

void
print_rhyme(rhyme_t rhyme)
{
  assert(rhyme);
  printf("rhyme: pts = %d, name = %s, key = ", rhyme->points, rhyme->player_name);
  print_key(rhyme->key);
}

bool
rhyme_eq (rhyme_t rhyme1, rhyme_t rhyme2)
{
  char * w1 = rhyme1->key->word;
  char * w2 = rhyme2->key->word;
  return (strcmp(w1, w2) == 0);
}

rhyme_t
new_rhyme(char * player_name, p_key * key, int points)
{
  rhyme_t rhyme = malloc(sizeof(rhyme_t));
  assert(rhyme);
  
  rhyme->player_name = player_name;
  rhyme->points = points;
  rhyme->key = key;
  
  return rhyme;
}

int
int_len(int num)
{
  int s = num < 0 ? 1 : 0;
  int len = 0;
  do
    {
      num = num / 10;
      len++;
    }
  while (num != 0);
  return s + len;
}

#define W_LEN 19

void
print_rhyme_sequence(rhyme_t_list_t * rhyme_sequence)
{
  rhyme_t_list_t * current = rhyme_sequence;
  assert(current);
  
  int i;

  printf("  CURRENT WORD     | Previous words\n");
  printf("  ");
  for (i = 0; i < 76; i++)
    {
      printf("-");
    }
  printf("\n");

  
  printf("->");
  int words_printed = 0;
  while (current != NULL && words_printed < 4)
    {
      char * word = current->head->key->word;
      int w_len = strlen(word);
      printf("%s", word);
      words_printed++;
      
      for (i = 0; i < W_LEN - w_len - 2; i++)
        {
          printf(" ");
        }
      
      printf("| ");
      current = current->tail;
    }

  printf("\n  ");
  for (i = 0; i < 76; i++)
    {
      printf("-");
    }
  current = rhyme_sequence;
  words_printed = 0;
  printf("\n  ");
  while (current != NULL && words_printed < 4)
    {
      char * name = current->head->player_name;
      int pts = current->head->points;
      int n_len = strlen(name);
      int p_len = int_len(pts);

      printf("%s", name);
      for (i = 0; i < W_LEN - n_len - p_len - 3; i++)
        {
          printf(" ");
        }

      printf("%d | ", pts);
      words_printed++;
      current = current->tail;
    }
  printf("\n\n");
}

void msg(const char * txt)
{
  printf("%s\n", txt);
  fflush(stdout);
}


int
score_pair(p_key * key1, p_key * key2)
{
  assert(key1->code);
  assert(key2->code);
  int_list_t * code1 = key1->code;
  int_list_t * code2 = key2->code;

  int len1 = int_list_length(code1);
  //int len2 = int_list_length(code2);
  float c = (float)len1 / 5.0f;
  
  int matches = 0;

  while (code1 && code2 && code1->head == code2->head)
  {
    code1 = code1->tail;
    code2 = code2->tail;
    matches += 1;
  }

  float weight = (float)(matches * c);
  
  if (weight < 1.0f)
    {
      return -5;
    }
  else
    {
      return (int)weight - 1;
    }
}


char *
robot_select(rhyme_t_list_t * rhyme_sequence, p_key ** p_data, int key_count)
{
  p_key * match_key = rhyme_sequence->head->key;
  rhyme_t test_rhyme;
  int score, best_score = 0;
  bool used;
  p_key * best_key = p_data[0];
  
  int i;
  for (i = 0; i < key_count - 1; i++)
    {
      test_rhyme = new_rhyme("", p_data[i], 0);
      used = rhyme_t_list_find(rhyme_sequence, test_rhyme, (*rhyme_eq));
      if (!used)
        {
          score = score_pair(match_key, p_data[i]);
          if (score > best_score)
            {
              best_key = p_data[i];
              best_score = score;
            }
        }
    }

  return best_key->word;
}



