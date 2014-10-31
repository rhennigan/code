#include <stdbool.h>
#include <stdio.h>

#define PIPE_READ 0
#define PIPE_WRITE 1

void err_chk (bool failed, const char *fail_msg);
int grep_fork (FILE * in);
