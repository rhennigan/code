// Copyright 2014 Richard Hennigan

#include "./lib/data/stack.h"

typedef char* str;

#ifndef _DEF_STACK_STR_
#define _DEF_STACK_STR_
DEF_LIST_BASE(str)
DEF_LIST_PRINT(str, "%s")
DEF_STACK_BASE(str)
DEF_STACK_PRINT(str)
#endif

#ifndef _DEF_STACK_CHAR_
#define _DEF_STACK_CHAR_
DEF_LIST_BASE(char)
DEF_LIST_PRINT(char, "'%c'")
DEF_STACK_BASE(char)
DEF_STACK_PRINT(char)
#endif

#ifndef _DEF_STACK_INT_
#define _DEF_STACK_INT_
DEF_LIST_FULL(int, "%d")
DEF_STACK_BASE(int)
DEF_STACK_PRINT(int)
#endif
