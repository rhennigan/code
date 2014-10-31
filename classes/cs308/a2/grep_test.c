/* #define _GNU_SOURCE */

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <assert.h>
#include <string.h>
#include <limits.h>
/* #include <fcntl.h> */
#include "util.h"




int
main (int argc, char * argv[])
{
  int linec = 0, batch_count;
  FILE *sort_data;
  
  if (argc == 1) {
    sort_data = fopen ("cs308a2_grep_data_2", "r");
  } else {
    sort_data = fopen (argv[1], "r");
  }

  if (sort_data == NULL)
    {
      printf("usage: %s [grep_data]\n", argv[0]);
      perror("fopen");
      exit(1);
    }

  while ((batch_count = grep_fork (sort_data)) != 0)
    {
      printf ("Counted %d lines in this batch\n", batch_count);
      linec += batch_count;
      printf ("Total lines so far: %d\n", linec);
    }

  fclose (sort_data);

  printf ("\n\nTotal line count: %d\n", linec);

  printf ("Done\n");
  exit (EXIT_SUCCESS);
}





void
err_chk (bool failed, const char *fail_msg)
{
  if (failed)
    {
      perror (fail_msg);
      exit (EXIT_FAILURE);
    }
}


int
grep_fork (FILE * in)
{
  int pipe_d[2], pipe_u[2];
  err_chk (pipe (pipe_d) == -1, "pipe: failed to open pipe_d");
  err_chk (pipe (pipe_u) == -1, "pipe: failed to open pipe_u");

  switch (fork ())
    {
    case -1:
      perror ("fork");
      exit (EXIT_FAILURE);

    case 0:
      err_chk (close (pipe_d[PIPE_WRITE]) == -1, "close: dw");
      err_chk (close (pipe_u[PIPE_READ]) == -1, "close: ur");

      err_chk (dup2 (pipe_d[PIPE_READ], STDIN_FILENO) == -1, "dup2");
      err_chk (dup2 (pipe_u[PIPE_WRITE], STDOUT_FILENO) == -1, "dup2");

      execlp ("grep", "grep", "123", NULL);

      // something went wrong if we got this far
      perror ("returned from execlp unexpectedly");
      exit (EXIT_FAILURE);

    default:
      err_chk (close (pipe_d[PIPE_READ]) == -1, "close: dr");
      err_chk (close (pipe_u[PIPE_WRITE]) == -1, "close: uw");

      char buffer[BUFSIZ];
      int sent_bytes = 0, lc = 0;

      while (fgets (buffer, BUFSIZ, in) != NULL)
	{
	  ssize_t wb = write (pipe_d[PIPE_WRITE], &buffer, strlen (buffer));
	  err_chk (wb == 0 || wb == -1, "write");
	  sent_bytes += wb;

	  if (sent_bytes >= PIPE_BUF * 512)	// if we exceed the system limit,
	    {			// count what we have so far
	      break;
	    }
	}

      err_chk (close (pipe_d[PIPE_WRITE]) == -1, "close: dw");	// send EOF
      FILE *fp = fdopen (pipe_u[PIPE_READ], "r");
      while (fgets (buffer, BUFSIZ, fp) != NULL)
	{
	  lc++;
	}
      fclose (fp);
      sent_bytes = 0;

      return lc;
    }
}
