#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/wait.h>
#include <assert.h>
#include <string.h>
#include "util.h"


int
main ( /* int argc, char * argv[] */ )
{
  int pipe_d[2], pipe_u[2];

  // Open two pipes
  err_chk (pipe (pipe_d) == -1, "pipe: failed to open pipe_d");
  err_chk (pipe (pipe_u) == -1, "pipe: failed to open pipe_u");
  printf ("Opened pipe_d (r:%d, w:%d)\n", pipe_d[PIPE_READ],
	  pipe_d[PIPE_WRITE]);
  printf ("Opened pipe_u (r:%d, w:%d)\n", pipe_u[PIPE_READ],
	  pipe_u[PIPE_WRITE]);


  // Create a child process
  pid_t pID = fork ();

  switch (pID)
    {

      /* FAILURE */
    case -1:
      perror ("fork");
      exit (EXIT_FAILURE);


      /* CHILD PROCESS */
    case 0:

      // close write end of downstream pipe
      err_chk (close (pipe_d[PIPE_WRITE]) == -1, "close: dw");

      // close read end of upstream pipe
      err_chk (close (pipe_u[PIPE_READ]) == -1, "close: ur");



      // Message testing
      char c_msg_out[BUFSIZ] = "uw";
      char c_msg_in[BUFSIZ];


      // get message from parent
      ssize_t r_bytes_c = read (pipe_d[PIPE_READ], &c_msg_in, BUFSIZ);
      err_chk (r_bytes_c == 0, "read: unexpected EOF");
      err_chk (r_bytes_c == -1, "read");
      printf ("CHILD:  writing on %d OK\n", pipe_d[PIPE_WRITE]);

      if (strcmp (c_msg_in, "dw") == 0)
	{
	  printf ("CHILD:  reading on %d OK\n", pipe_d[PIPE_READ]);
	  fflush (stdout);
	}
      else
	{
	  printf ("CHILD:  unexpected message from parent\n");
	  exit (EXIT_FAILURE);
	}


      // send a response
      ssize_t w_bytes_c = write (pipe_u[PIPE_WRITE], &c_msg_out, BUFSIZ);
      err_chk (w_bytes_c == 0 || w_bytes_c == -1, "write");


      // redirect stdout and stdin
      printf
	("CHILD:  duplicating downstream read (%d) onto stdin (%d)\n",
	 pipe_d[PIPE_READ], STDIN_FILENO);

      dup2 (pipe_d[PIPE_READ], STDIN_FILENO);

      printf
	("CHILD:  duplicating upstream write (%d) onto stdout (%d)\n",
	 pipe_u[PIPE_WRITE], STDOUT_FILENO);

      dup2 (pipe_u[PIPE_WRITE], STDOUT_FILENO);

      printf ("ready");
      fflush (stdout);



      // starting sort
      execlp ("sort", "sort", "-k3,3", "-k1,1", NULL);


      // something went wrong if we got this far
      perror ("returned from execlp unexpectedly");
      exit (EXIT_FAILURE);


      /* PARENT PROCESS */
    default:

      // close read end of downstream pipe
      err_chk (close (pipe_d[PIPE_READ]) == -1, "close: dr");

      // close write end of upstream pipe
      err_chk (close (pipe_u[PIPE_WRITE]) == -1, "close: uw");



      // Message testing
      char p_msg_out[BUFSIZ] = "dw";
      char p_msg_in[BUFSIZ];


      // send message to child
      ssize_t w_bytes_p = write (pipe_d[PIPE_WRITE], &p_msg_out, BUFSIZ);
      err_chk (w_bytes_p == 0 || w_bytes_p == -1, "write");


      // get response from child
      ssize_t r_bytes_p = read (pipe_u[PIPE_READ], &p_msg_in, BUFSIZ);
      err_chk (r_bytes_p == 0, "read: unexpected EOF");
      err_chk (r_bytes_p == -1, "read");
      printf ("PARENT: writing on %d OK\n", pipe_u[PIPE_WRITE]);

      if (strcmp (p_msg_in, "uw") == 0)
	{
	  printf ("PARENT: reading on %d OK\n", pipe_u[PIPE_READ]);
	  fflush (stdout);
	}
      else
	{
	  perror ("PARENT: unexpected message from child");
	  exit (EXIT_FAILURE);
	}



      // see if stdout was redirected successfully
      char buffer[BUFSIZ];
      r_bytes_p = read (pipe_u[PIPE_READ], &buffer, BUFSIZ);
      err_chk (r_bytes_p == 0, "read: unexpected EOF");
      err_chk (r_bytes_p == -1, "read");
      printf ("PARENT: child reports: %s\n", buffer);
      fflush (stdout);


      // ready to start sending data for sorting
      FILE *sort_data = fopen ("cs308a2_sort_data", "r");
      while (fgets (buffer, BUFSIZ, sort_data) != NULL)	// get one line
	{
	  // send line of data to child running sort
	  w_bytes_p = write (pipe_d[PIPE_WRITE], &buffer, strlen (buffer));
	  err_chk (w_bytes_p == 0 || w_bytes_p == -1, "write");
	}


      // once fgets returns null, we hit EOF.
      // we'll close the pipe to child to trigger an EOF downstream.
      err_chk (close (pipe_d[PIPE_WRITE]) == -1, "close: dw");

      // don't need the input file handle anymore
      fclose (sort_data);


      // now we'll await results and print them
      int prev_ac = 0, ac_count = 0;
      char name1[BUFSIZ], name2[BUFSIZ];
      int ac, p1, p2;

      FILE *fp = fdopen (pipe_u[PIPE_READ], "r");

      printf ("\n");
      while (fgets (buffer, BUFSIZ, fp) != NULL)
	{
	  buffer[strlen (buffer) - 1] = '\0';
	  sscanf (buffer, "%511s %511s %3d %3d %4d", name1, name2, &ac, &p1,
		  &p2);
	  ac_count++;

	  if (ac != prev_ac)
	    {
	      printf ("  Area code %d: %d instances\n", ac, ac_count);
	      ac_count = 0;
	    }

	  prev_ac = ac;
	}

      printf ("\n");

      // clean up
      err_chk (close (pipe_u[PIPE_READ]) == -1, "close: ur");
      printf ("PARENT: waiting for child process to terminate\n");
      wait (NULL);
      printf ("PARENT: all done, exiting\n");
      exit (EXIT_SUCCESS);
    }

  // if we get here, something went wrong
  printf ("We shouldn't be here...\n");
  exit (EXIT_FAILURE);
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
