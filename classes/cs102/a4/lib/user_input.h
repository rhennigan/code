#ifndef _USER_INPUT_H
#define _USER_INPUT_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>
#include <stdbool.h>


#define WAIT()                                                                  \
  char ch;                                                                      \
  printf( "Press [ENTER] to continue..." );                                     \
  fflush(stdout);                                                               \
  while ((ch = getchar()) != '\n' && ch != EOF);                                \

char *
get_input_string()
{
  fflush(stdout);
  char * input = malloc(sizeof(char) * BUFSIZ);
  assert(input);

  fgets(input, BUFSIZ, stdin);

  int i;
  for (i = 0; i < BUFSIZ; i++)
  {
    if (input[i] == '\n')
    {
      input[i] = '\0';
    }
  }
  
  return input;
}


char *
lowercase(const char * str)
{
  char * lower = malloc(strlen(str) + 1);
  assert(lower);
  int i;
  for (i = 0; str[i]; i++)
    {
      lower[i] = tolower(str[i]);
    }
  return lower;
}


int
get_input_int(int min, int max)
{
  char * input = malloc(sizeof(char) * BUFSIZ);
  assert(input);
  char * output = malloc(sizeof(char) * BUFSIZ);
  assert(output);

  int digit, number, exponent;

  int i, j, k;
  while (1)
  {
    digit = 0;
    number = 0;
    exponent = 1;

    fgets(input, BUFSIZ, stdin);
    fflush(stdin);

    i = 0;
    j = 0;
    k = 0;

    for (i = 0; i < BUFSIZ; i++)
    {
      if (input[i] == '\n')
      {
        break;
      }

      digit = input[i] - '0';

      if ((0 <= digit) && (digit <= 9))
      {
        output[j++] = digit;
      }
    }

    for (k = j - 1; k >= 0; k--)
    {
      number += exponent * output[k];
      exponent *= 10;
    }

    if ((min <= number) && (number <= max))
    {
      break;
    }
    else
    {
      printf("  Invalid input. Please enter a number between %d and %d\n", min, max);
    }
  }

  return number;
}




bool
get_input_bool()
{
  while (1)
    {
      fflush(stdout);
      char * input = malloc(sizeof(char) * BUFSIZ);
      assert(input);

      fgets(input, BUFSIZ, stdin);

      int i;
      for (i = 0; i < BUFSIZ; i++)
        {
          if (input[i] == '\n')
            {
              input[i] = '\0';
            }
        }

      if (strcmp(input, "y") == 0)
        {
          free(input);
          return true;
        }
      else if (strcmp(input, "n") == 0)
        {
          free(input);
          return false;
        }
      else
        {
          printf("  Invalid response. Please enter \"y\" or \"n\": ");
        }
    }
}


#endif
