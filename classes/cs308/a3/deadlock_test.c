#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <signal.h>
#include <assert.h>
#include "./donuts.h"

#define TEST_COUNT 20
#define TIMEOUT 1
#define MS * 1000

/*
  These set up the testing domain limits and resolution
  The total number of tests that will need to run is given by:
  
    N = TEST_COUNT * (SH - SL) / SS * (DH - DL) / DS * (CH - CL) / CS
*/
#define CL 1   // consumers start value
#define CH 10  // consumers end value
#define CS 1   // consumers step size

#define DL 10  // dozens start value
#define DH 10  // dozens end value
#define DS 1   // dozens step size

#define SL 1   // slots start value
#define SH 50  // slots end value
#define SS 1   // slots step size

int shmid, semid[3];

int get_timestamp(char *file);

int main(int argc, char *argv[]) {
  char slots_str[BUFSIZ];
  char dozens_str[BUFSIZ];
  int slots_i, dozens_i, consumers_i;
  FILE *data = fopen("data.csv", "a");

  system("touch ./.prodlk");
  system("touch ./.conslk");

  for (consumers_i = CL; consumers_i <= CH; consumers_i += CS) {
    for (dozens_i = DL; dozens_i <= DH; dozens_i += DS) {
      for (slots_i = SL; slots_i <= SH; slots_i += SS) {
        printf("\n\n--------------------------\n");
        printf(" TEST CONFIGURATION\n");
        printf("--------------------------\n");
        printf(" slots = %d\n", slots_i);
        printf(" dozens = %d\n", dozens_i);
        printf(" consumers = %d\n\n", consumers_i);
        printf("--------------------------\n");

        snprintf(slots_str, BUFSIZ, "%d", slots_i);
        snprintf(dozens_str, BUFSIZ, "%d", dozens_i);
        int dl_count = 0;

        /* we run TEST_COUNT tests and average the results for the current
           values of consumers_i, dozens_i, and slots_i */
        int test_num;
        for (test_num = 0; test_num < TEST_COUNT; test_num++) {
          printf("\nRunning test number %d of %d\n", test_num + 1, TEST_COUNT);

          /* start producer process */
          pid_t prod_pid;
          if ((prod_pid = fork()) == -1) {
            perror("fork");
            exit(EXIT_FAILURE);
          } else if (prod_pid == 0) {
            fflush(stdout);
            freopen("log/prod.log", "w", stdout);
            execl("./proddonuts", "proddonuts", slots_str, NULL);
          }

          /* wait a little to make sure the producer has set up everything */
          usleep(500 MS);

          /* start consumers_i consumer processes */
          int consumer_num;
          pid_t cons_pid[consumers_i];
          for (consumer_num = 0; consumer_num < consumers_i; consumer_num++) {
            if ((cons_pid[consumer_num] = fork()) == -1) {
              perror("fork");
              exit(EXIT_FAILURE);
            } else if (cons_pid[consumer_num] == 0) {
              /* each consumer process gets its own log file */
              char cons_log[BUFSIZ], cnum_str[BUFSIZ];
              snprintf(cons_log, BUFSIZ, "log/cons_%d.log", consumer_num);
              snprintf(cnum_str, BUFSIZ, "%d", consumer_num);
              fflush(stdout);
              /* redirect stdout to the consumer's log file */
              freopen(cons_log, "w", stdout);
              execl("./consdonuts", "consdonuts",
                    cnum_str, slots_str, dozens_str, NULL);
              fflush(stdout);
            }
          }

          int status, pt, ct, finished;
          /* run until either all consumers finish on their own (no deadlock)
             or a deadlock is detected, in which case the remaining consumers
             are terminated */
          while (1) {  // checking on consumers
            /* Check if all consumers have finished running */
            finished = 1;
            for (consumer_num = 0; consumer_num < consumers_i; consumer_num++) {
              if (!waitpid(cons_pid[consumer_num], &status, WNOHANG)) {
                finished = 0;
              }
            }

            /* If all consumers are finished, no deadlock has taken place */
            if (finished) {
              printf("All consumers have finished running\n");
              printf("  now quitting producer process...\n");
              kill(prod_pid, SIGKILL);  // zombies are cleaned up later
              break;
            }

            /* consumers aren't done yet, so we'll wait a little bit and then
               check on them */
            usleep(100 MS);

            /* Every time a consumer is able to grab a donut, it touches the
               consumer lock file which updates its timestamp. Similarly, the
               producer process does the same when it is able to insert another
               donut. If no updates have been made in a while, it almost
               certainly means we have a deadlock*/
            pt = time(NULL) - get_timestamp("./.prodlk");  // time since last
            ct = time(NULL) - get_timestamp("./.conslk");  //   update

            if (pt > TIMEOUT || ct > TIMEOUT) {  // deadlock detected!
              printf("\n--------------------------\n");
              printf("*** Deadlock detected! ***\n");
              printf("--------------------------\n");
              printf("Sending kill signal to the following consumers:\n");

              /* terminate any consumers that are still running */
              int i;
              for (i = 0; i < consumers_i; i++) {
                if (!waitpid(cons_pid[i], &status, WNOHANG)) {
                  printf("  %d (pid = %d)\n", i, cons_pid[i]);
                  kill(cons_pid[i], SIGKILL);
                }
              }

              /* terminate the producer */
              printf("All consumers are now stopped\n");
              printf("  now quitting producer process...\n\n");
              kill(prod_pid, SIGKILL);

              // increment the deadlock counter
              dl_count++;
              break;
            }  // end deadlock detected!
          }  // end checking on consumers
        }

        /* proportion of the tests which were deadlocked */
        double dl_m = (double) dl_count / (double) TEST_COUNT;

        printf("\n--------------------------\n");
        printf(" RESULTS\n");
        printf("--------------------------\n");
        printf("  deadlock count:       %d\n", dl_count);
        printf("  total runs:           %d\n", TEST_COUNT);
        printf("  proportion:         %.2f\n", dl_m);
        printf("--------------------------\n");
        printf("\n\n");

        /* save the results to a csv file */
        fprintf(data, "%d, %d, %d, %d, %d, %f\n",
                slots_i, dozens_i, consumers_i, dl_count, TEST_COUNT, dl_m);

        fflush(NULL);

        // prevent the zombie apocalypse
        printf("Preventing the zombie apocalypse...\n");
        fflush(NULL);
        while (wait(NULL) > 0) {}
        printf("  all child processes terminated\n\n");
      }
    }
  }

  fclose(data);

  exit(EXIT_SUCCESS);
}

/* returns the last accessed time of the given file in UNIX time */
int get_timestamp(char *file) {
  struct stat fs;
  if (stat(file, &fs) == -1) {
    perror("stat");
    exit(EXIT_FAILURE);
  }
  return (int) fs.st_atime;
}
