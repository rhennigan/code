#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <stdbool.h>
#include "lib/user_input.h"

typedef char_stack_t;
char_stack_t * char_stack_init();
char_stack_t * char_stack_push(char_stack_t * stack, char obj);
char char_stack_peek(char_stack_t * stack);
char char_stack_pop(char_stack_t ** stack_addr);
bool char_stack_isempty(char_stack_t * stack);
void char_stack_dispose(char_stack_t ** stack_addr);
void char_stack_print(char_stack_t * stack);

typedef int_stack_t;
int_stack_t * int_stack_init();
int_stack_t * int_stack_push(int_stack_t * stack, int obj);
int int_stack_peek(int_stack_t * stack);
int int_stack_pop(int_stack_t ** stack_addr);
bool int_stack_isempty(int_stack_t * stack);
void int_stack_dispose(int_stack_t ** stack_addr);
void int_stack_print(int_stack_t * stack);

char match(char ch) {
  switch (ch) {
    case '(':
      return ')';
    case ')':
      return '(';
    case '[':
      return ']';
    case ']':
      return '[';
    case '{':
      return '}';
    case '}':
      return '{';
    default:
      return ch;
  }
}

bool isbracket(char ch) {
  return
      ch == '(' || ch == ')' ||
      ch == '{' || ch == '}' ||
      ch == '[' || ch == ']';
}

int main(int argc, char *argv[]) {
  printf("Enter a path for expressions.txt or press enter for the default: ");
  char * _path = get_input_string();
  char * path = (strcmp(_path, "") == 0) ? "resources/expressions.txt" : _path;
  FILE * expression_src = fopen(path, "r");

  char line[BUFSIZ];
  int line_num = 0;

  while (fgets(line, BUFSIZ, expression_src) != NULL) {
    line_num++;
    char_stack_t * bracket_stack = char_stack_init();
    int i;
    bool valid = true;
    for (i = 0; i < strlen(line) && valid; i++) {
      if (isbracket(line[i])) {
        switch (line[i]) {
          case '(':
            bracket_stack = char_stack_push(bracket_stack, '(');
            break;
          case '{':
            bracket_stack = char_stack_push(bracket_stack, '{');
            break;
          case '[':
            bracket_stack = char_stack_push(bracket_stack, '[');
            break;
          default:
            if (char_stack_peek(bracket_stack) == match(line[i])) {
              char_stack_pop(&bracket_stack);
            } else {
              valid = false;
            }
            break;
        }
      }
    }
    valid = char_stack_isempty(bracket_stack) && valid;
    if (valid) {
      printf("line %d: %s OK!\n\n", line_num, line);
    } else {
      printf("line %d: %s", line_num, line);
      int j;
      for (j = 0; j < i + 7; j++) {
        printf(" ");
      }
      if (char_stack_isempty(bracket_stack)) {
        printf("^ error: '%c' is unexpected here\n\n", line[i - 1]);
      } else {
        char left = char_stack_peek(bracket_stack);
        printf("^ error: there should be a '%c' here\n\n", match(left));
      }
    }
  }

  return 0;
}
