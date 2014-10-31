// Copyright 2014 Richard Hennigan

#include <stdio.h>
#include <stdbool.h>

typedef str;
typedef str_stack_t;
str_stack_t * str_stack_init();
str_stack_t * str_stack_push(str_stack_t * stack, str obj);
str str_stack_peek(str_stack_t * stack);
str str_stack_pop(str_stack_t ** stack_addr);
bool str_stack_isempty(str_stack_t * stack);
void str_stack_dispose(str_stack_t ** stack_addr);
void str_stack_print(str_stack_t * stack);

int main(int argc, char *argv[]) {
  printf("\nTESTING STACK FUNCTIONS\n");
  printf("-----------------------\n\n");

  // Initialize the stack
  printf("Initialize the stack:\n");
  str_stack_t * stack = str_stack_init();
  printf("stack = ");
  str_stack_print(stack);

  // Check if empty
  printf("\nCheck if empty:\n");
  printf("stack empty = %s\n", str_stack_isempty(stack) ? "true" : "false");

  // Push a few items
  printf("\nPush a few items:\n");
  stack = str_stack_push(stack, "first item");
  stack = str_stack_push(stack, "second item");
  stack = str_stack_push(stack, "third item");
  printf("stack = ");
  str_stack_print(stack);

  // Check if empty
  printf("\nCheck if empty:\n");
  printf("stack empty = %s\n", str_stack_isempty(stack) ? "true" : "false");

  // Peek and display
  printf("\nPeek and display:\n");
  str peek_test = str_stack_peek(stack);
  printf("peek_test = %s\n", peek_test);
  printf("stack = ");
  str_stack_print(stack);

  // Pop and display all the items
  printf("\nPop and display all the items\n");
  str pop_test = str_stack_pop(&stack);
  printf("pop_test = %s\n", pop_test);
  printf("stack = ");
  str_stack_print(stack);

  // Check if empty
  printf("\nCheck if empty:\n");
  printf("stack empty = %s\n", str_stack_isempty(stack) ? "true" : "false");

  // Cleanup
  str_stack_dispose(&stack);
  return 0;
}
