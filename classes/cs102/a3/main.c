#define _CRT_SECURE_NO_WARNINGS
#define DATA_LENGTH 133389

#include <time.h>
#include <stdlib.h>
#include <ctype.h>
#include "lib/player.h"
#include "lib/user_input.h"
#include "lib/rhyme.h"

#define _DEBUG false

void print_header(const char * label)
{
  int len = strlen(label);
  printf("\n\n");
  printf("%s\n", label);
  int i;
  for (i = 0; i < len; i++)
    {
      printf("-");
    }
  printf("\n\n");
  fflush(stdout);
}


int main()
{
  char BUFFER[BUFSIZ];
  memset(BUFFER, '\0', BUFSIZ);
  
  srand(time(NULL));
  
  print_header("SETUP - Import Data");
  printf("  Enter the path and filename for the location of the CMU dictionary\n");
  printf("  Leave blank for default (resources/cmudict.0.7a).\n");
  printf("  > ");
  char * _path = _DEBUG ? "resources/cmudict.0.7a" : get_input_string();
  
  printf("  Loading...");
  fflush(stdout);
  char * path = (strcmp(_path, "") == 0) ? "resources/cmudict.0.7a" : _path;
  p_key * p_data[DATA_LENGTH];
  int key_count = load_all_keys(path, p_data);
  printf("  Rhyme data loaded.\n");
  fflush(stdout);

  int i = 0;
  for (i = 0; i < key_count; i++)
    {
      assert(p_data[i]);
    }


  
  print_header("SETUP - Players");

  int player_count = 0;
  bool more_players = true;
  player_t_clist_t * player_list = NULL;
  
  while (more_players)
    {
      player_count += 1;
      printf("  Enter the name of player %d: ", player_count);
      char * name = _DEBUG ? "DEBUG" : get_input_string();

      printf("  Do you want the computer to control this player? (y/n): ");
      bool control = _DEBUG ? true : get_input_bool();

      player_t player = player_new(player_count, name, 5, control);

      if (player_list == NULL)
        {
          player_list = player_t_clist_init(player);
        }
      else
        {
          player_list = player_t_clist_app(player_list, player);
        }

      show_player_list(player_list);

      if (player_list->prev != player_list)
        {
          printf("  Add more players? (y/n): ");
          more_players = _DEBUG ? false : get_input_bool();
        }
      printf("\n");
    }


  /*                                                                                    */
  print_header("INSTRUCTIONS");
  printf("  Players attempt to come up with words that rhyme with the last word of a\n");
  printf("  rhyme sequence. Each time a new word is entered, it becomes the last word\n");
  printf("  in the sequence and the next player must try to come up with a word that\n");
  printf("  rhymes with it. If the sequence is empty, a random word is selected.\n");
  printf("    Players are awarded points for a word based on how closely it rhymes\n");
  printf("  with the previous word. If the word doesn't rhyme at all, the player\n");
  printf("  receives negative points. If a player's total score drops below zero, they\n");
  printf("  are eliminated from the game.\n\n");

  WAIT();



  rhyme_t rhyme = new_rhyme("Start", p_data[rand() % key_count], 0);
  rhyme_t_list_t * rhyme_sequence = rhyme_t_list_init(rhyme);
  while (1)
    {
      int temp_pts = -5;
      int tpts = -5;
      int fail_count = 0;
      /* char * new_word = (char*)malloc(BUFSIZ); */
      char new_word[BUFSIZ];
      printf("\n\n\n\n");
      
      if (player_list == player_list->prev)
        {
          print_header("GAME OVER");
          printf("  %s wins the game!\n", player_list->data->name);
          exit(EXIT_SUCCESS);
        }
      
      print_header("NEXT TURN");
      print_rhyme_sequence(rhyme_sequence);
      printf("  It is now %s's turn.\n", player_list->data->name);

      rhyme_t current_rhyme;
      p_key * key = NULL;
  
      while (key == NULL)
        {
          printf("  Enter a word that rhymes with \"%s\".\n  > ", rhyme_sequence->head->key->word);

          if (player_list->data->control) // Robot player
            {
              printf("Thinking");
                            
              int score = 0;
              int best_score = 0;
              int best_idx = 0;

              int i;
              for (i = 0; i < key_count - 1; i++)
                {
                  if (i % (key_count / 30) == 0)
                    {
                      printf(".");
                      fflush(stdout);
                    }

                  assert(p_data[i]);
                  rhyme_t test_rhyme = new_rhyme(BUFFER, p_data[i], 0);
                  assert(test_rhyme);
                  //print_rhyme(test_rhyme);
                  
                  bool used = rhyme_t_list_find(rhyme_sequence, test_rhyme, (*rhyme_eq));
                  if (!used)
                    {
                      score = score_pair(rhyme_sequence->head->key, p_data[i]);
                     
                      if (score > best_score)
                        {
                          best_idx = i;
                          best_score = score;
                        }
                    }
                  free(test_rhyme);
                }
              
              if (best_score == 0)
                {
                  best_idx = rand() % key_count - 1;
                }
              /* new_word = p_data[best_idx]->word; */
              strcpy(new_word, p_data[best_idx]->word);
              printf("\n\n");
              fflush(stdout);
            }
          
          else // Human player
            {
              char * str = get_input_string();
              strcpy(new_word, str);
              /* new_word = get_input_string(); */
            }

          /* Search database for the word */
          int i;
          
          p_key * temp_key = NULL;
          rhyme_t test_rhyme = NULL;
          
          for (i = 0; i < key_count; i++)
            {
              if (strcmp(p_data[i]->word, new_word) == 0) // found it
                {
                  key = p_data[i];
                  assert(key);
                  int j = i;
                  while (j < key_count && strcmp(p_data[j]->word, new_word) == 0)
                    {
                      temp_key = p_data[j];
                      assert(temp_key);
                      test_rhyme = new_rhyme(player_list->data->name, temp_key, 0);

                      if (rhyme_t_list_find(rhyme_sequence, test_rhyme, (*rhyme_eq)))
                        {
                          printf("\n  %s has already been used!", new_word);
                          tpts = -5;
                          break;
                        }
                      else
                        {
                          temp_pts = score_pair(temp_key, rhyme_sequence->head->key);
                          if (temp_pts > tpts)
                            {
                              key = temp_key;
                              tpts = temp_pts;
                            }
                        }
                      j++;
                    }
                  break;
                }
            }

          if (key == NULL)
            {
              printf("\n  Unable to parse word \"%s\". Please try another word.\n", new_word);
              fail_count++;
              if (fail_count > 3)
                {
                  printf("\n  Are you making up words? You lose 1 point.\n");
                  fail_count = 0;
                  tpts = -1;
                  break;
                }
            }
          else
            {
              break;
            }
        }

      
      printf("\n  You get %d points for %s.\n", tpts, new_word);

      if (tpts < 0)
        {
          printf("\n  A new random word will be chosen for the sequence...\n");
          key = p_data[rand() % key_count - 1];
          assert(key);
          current_rhyme = new_rhyme("Start", key, 0);
          rhyme_t_list_dispose(rhyme_sequence);
          rhyme_sequence = rhyme_t_list_init(current_rhyme);
        }
      else
        {
          assert(key);
          current_rhyme = new_rhyme(player_list->data->name, key, tpts);
        }
        
      
      rhyme_sequence = rhyme_t_list_cons(rhyme_sequence, current_rhyme);
      player_list->data->score = player_list->data->score + tpts;

      if (player_list->data->score < 0)
        {
          printf("\n\n  !!! %s has been eliminated !!!\n", player_list->data->name);
          player_t_clist_t * new_player_list = player_t_clist_delete(player_list);
          player_t_clist_dispose(player_list);
          player_list = new_player_list;
        }
      else
        {
          player_list = player_list->next;
        }

      show_player_list(player_list);

      if (!_DEBUG) { WAIT(); };
    }

  
  printf("\n\n\n");
  
  return 0;
}
