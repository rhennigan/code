#ifndef _LIB_MATH_EXPRESSIONS_
#define _LIB_MATH_EXPRESSIONS_

#include "./rationals.h"
#include "../data/stack.h"

typedef char* expression_t;

#ifndef _DEF_STACK_CHAR_
#define _DEF_STACK_CHAR_
DEF_LIST_BASE(char)
DEF_LIST_PRINT(char, "'%c'")
DEF_STACK_BASE(char)
DEF_STACK_PRINT(char)
#endif

#ifndef _DEF_STACK_RATIONAL_T_
#define _DEF_STACK_RATIONAL_T_
DEF_LIST_BASE(rational_t)
DEF_STACK_BASE(rational_t)
#endif

void rational_t_print(rational_t q) {
  printf("%s, ", q_to_string(q));
}

void rational_t_stack_print(rational_t_stack * stack) {
  rational_t_list_iter(stack, (*rational_t_print));
}

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

bool isoperator(char ch) {
  return
      ch == '*' || ch == '/' ||
      ch == '+' || ch == '-';
}

int parse_digit(char ch) {
  return static_cast<int>(ch - '0');
}

rational_t unstack_digits(char_stack_t ** digit_stack) {
  if (char_stack_isempty(digit_stack)) {
    printf("can't unstack an empty stack\n");
    exit(EXIT_FAILURE);
  } else {
    int digit = 0, number = 0, exponent = 1;
    while (!char_stack_isempty(digit_stack)) {
      number += exponent * parse_digit(char_stack_pop(digit_stack));
      exponent *= 10;
    }
    return int_to_q(number);
  }
}



#endif  // _LIB_MATH_EXPRESSIONS_
