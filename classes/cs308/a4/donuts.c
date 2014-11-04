#include <stdlib.h>
#include <stdio.h>
#include "./donuts.h"

donut_ring_t shared_ring;
pthread_mutex_t prod[MAXFLAVORS];
pthread_mutex_t cons[MAXFLAVORS];
pthread_cond_t prod_cond[MAXFLAVORS];
pthread_cond_t cons_cond[MAXFLAVORS];
pthread_t thread_id[MAXCONSUMERS + MAXPRODUCERS];
pthread_t sig_wait_id;

#define numflavors   MAXFLAVORS
#define numslots     MAXSLOTS
#define numconsumers MAXCONSUMERS
#define numproducers MAXPRODUCERS

int main(int argc, char *argv[]) {
  int nsigs;
  struct timeval randtime, first_time, last_time;
  struct sigaction new_act;
  int arg_array[MAXCONSUMERS];
  sigset_t all_signals;

  int sigs[] = { SIGBUS, SIGSEGV, SIGFPE };

  pthread_attr_t thread_attr;
  struct sched_param shed_struct;

  int i, j, k;

  /**********************************************************************/
  /* INITIAL TIMESTAMP VALUE FOR PERFORMANCE MEASURE                    */
  /**********************************************************************/

  gettimeofday(&first_time, (struct timezone *) 0);
  for (i = 0; i < numconsumers + 1; i++) {
    arg_array[i] = i;  /* SET ARRAY OF ARGUMENT VALUES */
  }

  /**********************************************************************/
  /* GENERAL PTHREAD MUTEX AND CONDITION INIT AND GLOBAL INIT           */
  /**********************************************************************/

  for (i = 0; i < numflavors; i++) {
    pthread_mutex_init(&prod[i], NULL);
    pthread_mutex_init(&cons[i], NULL);
    pthread_cond_init(&prod_cond[i], NULL);
    pthread_cond_init(&cons_cond[i], NULL);
    shared_ring.outptr[i] = 0;
    shared_ring.in_ptr[i] = 0;
    shared_ring.serial[i] = 0;
    shared_ring.spaces[i] = numslots;
    shared_ring.donuts[i] = 0;
  }

  /**********************************************************************/
  /* SETUP FOR MANAGING THE SIGTERM SIGNAL, BLOCK ALL SIGNALS           */
  /**********************************************************************/

  sigfillset(&all_signals);
  nsigs = sizeof(sigs) / sizeof(int);
  for (i = 0; i < nsigs; i++)
    sigdelset(&all_signals, sigs[i]);
  sigprocmask(SIG_BLOCK, &all_signals, NULL);
  sigfillset(&all_signals);
  for (i = 0; i < nsigs; i++) {
    new_act.sa_handler = sig_handler;
    new_act.sa_mask = all_signals;
    new_act.sa_flags = 0;
    if (sigaction(sigs[i], &new_act, NULL) == -1) {
      perror("can't set signals: ");
      exit(EXIT_FAILURE);
    }
  }

  printf("just before threads created\n");

  return 0;
}
