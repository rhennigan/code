#ifndef _LIB_USER_INPUT_H
#define _LIB_USER_INPUT_H

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>
#include <stdbool.h>


#define WAIT()                                                                 \
  char ch;                                                                     \
  printf("Press [ENTER] to continue...");                                      \
  fflush(stdout);                                                              \
  while ((ch = getchar()) != '\n' && ch != EOF) {}                             \

char * get_input_string();
char * lowercase(const char * str);
int get_input_int(int min, int max);
double get_input_double(double min, double max);
bool get_input_bool();

#endif
