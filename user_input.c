#include <stdio.h>
#include "../lib/user_input.h"

char * get_input_string() {
  fflush(stdout);
  char * input = malloc(sizeof(char) * BUFSIZ);
  fgets(input, BUFSIZ, stdin);
  int i;
  for (i = 0; i < BUFSIZ; i++) {
    if (input[i] == '\n') {
      input[i] = '\0';
    }
  }
  return input;
}

char * lowercase(const char * str) {
  char * lower = malloc(strlen(str) + 1);
  int i;
  for (i = 0; str[i]; i++) {
      lower[i] = tolower(str[i]);
    }
  return lower;
}

int get_input_int(int min, int max) {
  char * input = malloc(sizeof(char) * BUFSIZ);
  char * output = malloc(sizeof(char) * BUFSIZ);
  int digit, number, exponent;
  int i, j, k;
  while (true) {
    digit = number = 0;
    exponent = 1;
    fgets(input, BUFSIZ, stdin);
    fflush(stdin);

    i = j = j = 0;
    for (i = 0; i < BUFSIZ; i++) {
      if (input[i] == '\n') break;
      digit = input[i] - '0';
      if ((0 <= digit) && (digit <= 9)) {
        output[j++] = digit;
      }
    }

    for (k = j - 1; k >= 0; k--) {
      number += exponent * output[k];
      exponent *= 10;
    }

    if ((min <= number) && (number <= max)) {
      break;
    } else {
      printf("  Invalid input. Please enter a number between %d and %d\n",
             min, max);
    }
  }
  return number;
}

double get_input_double(double min, double max) {
  char * input = malloc(sizeof(char) * BUFSIZ);
  char * output = malloc(sizeof(char) * BUFSIZ);
  int digit, int_part, exponent, decimal_place;
  double d_exp = 0.1, frac_part = 0.0, number;
  int i, j, k;
  while (true) {
    digit = int_part = 0;
    exponent = 1;
    fgets(input, BUFSIZ, stdin);
    fflush(stdin);

    i = j = k = 0;
    for (i = 0; i < BUFSIZ; i++) {
      if (input[i] == '.') decimal_place = i;
      if (input[i] == '\n') break;
      digit = input[i] - '0';
      if ((0 <= digit) && (digit <= 9)) {
        output[j++] = digit;
      }
    }

    for (k = decimal_place - 1; k >= 0; k--) {
      int_part += exponent * output[k];
      exponent *= 10;
    }

    for (k = decimal_place; k < j; k++) {
      frac_part += d_exp * output[k];
      d_exp *= 0.1;
    }

    number = (double)int_part + frac_part;

    if ((min <= number) && (number <= max)) {
      break;
    } else {
      printf("  Read: %f\n", number);
      printf("  Invalid input. Please enter a number between %.3f and %.3f\n",
             min, max);
    }
  }
  return number;
}

bool get_input_bool() {
  while (true) {
    int i;
    char * input = malloc(sizeof(char) * BUFSIZ);
    fgets(input, BUFSIZ, stdin);
    fflush(stdin);
    for (i = 0; i < BUFSIZ; i++) {
      if (input[i] == '\n') input[i] = '\0';
    }
    if (strcmp(input, "y") == 0) {
      free(input);
      return true;
    } else if (strcmp(input, "n") == 0) {
      free(input);
      return false;
    } else {
      printf("  Invalid response. Please enter \"y\" or \"n\": ");
    }
  }
}
