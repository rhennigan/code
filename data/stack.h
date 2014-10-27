#ifndef _LIB_DATA_STACK_H_
#define _LIB_DATA_STACK_H_

#include <stdbool.h>
#include "./linked_list.h"

#define DEF_STACK_TYPE(TYPE)                    \
  typedef TYPE##_list_t TYPE##_stack_t;

#define DEF_STACK_PRINT(TYPE)                           \
  void TYPE##_stack_print(TYPE##_stack_t * stack) {     \
    TYPE##_list_print(stack);                           \
  }

#define DEF_STACK_INIT(TYPE)                            \
  TYPE##_stack_t * TYPE##_stack_init() {                \
    return NULL;                                        \
  }

#define DEF_STACK_PUSH(TYPE)                                            \
  TYPE##_stack_t * TYPE##_stack_push(TYPE##_stack_t * stack, TYPE obj) { \
    return TYPE##_list_cons(stack, obj);                                \
  }

#define DEF_STACK_PEEK(TYPE)                            \
  TYPE TYPE##_stack_peek(TYPE##_stack_t * stack) {      \
    if (stack != NULL) {                                \
      return stack->head;                               \
    } else {                                            \
      return NULL;                                      \
    }                                                   \
  }

#define DEF_STACK_POP(TYPE)                             \
  TYPE TYPE##_stack_pop(TYPE##_stack_t ** stack_addr) { \
    TYPE obj = TYPE##_stack_peek(*stack_addr);          \
        free(*stack_addr);                              \
        (*stack_addr) = (*stack_addr)->tail;            \
        return obj;                                     \
  }

#define DEF_STACK_ISEMPTY(TYPE)                         \
  bool TYPE##_stack_isempty(TYPE##_stack_t * stack) {   \
    return (stack == NULL) ? 1 : 0;                     \
  }

#define DEF_STACK_DISPOSE(TYPE)                                 \
  void TYPE##_stack_dispose(TYPE##_stack_t ** stack_addr) {     \
    TYPE##_list_dispose(stack_addr);                            \
  }

#define DEF_STACK_BASE(TYPE)                    \
  DEF_STACK_TYPE(TYPE)                          \
  DEF_STACK_INIT(TYPE)                          \
  DEF_STACK_PUSH(TYPE)                          \
  DEF_STACK_PEEK(TYPE)                          \
  DEF_STACK_POP(TYPE)                           \
  DEF_STACK_ISEMPTY(TYPE)                       \
  DEF_STACK_DISPOSE(TYPE)

#endif   // _LIB_DATA_STACK_H_
