// utils.c - stuff
// Copyright (C) 2014 Richard Hennigan

#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include "./utils.h"

void check_fail(bool cond, const char * f, const char * msg) {
  if (cond) {
    printf("check_fail:\n");
    printf("  %s: %s\n", f, msg);
    exit(EXIT_FAILURE);
  }
}
