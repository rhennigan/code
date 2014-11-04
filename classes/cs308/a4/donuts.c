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

void init_timestamps(struct timeval first_time, int arg_array[]) {
  gettimeofday(&first_time, (struct timezone *) 0);
  int i;
  for (i = 0; i < numconsumers + 1; i++) {
    arg_array[i] = i;  /* SET ARRAY OF ARGUMENT VALUES */
  }
}
void init_mutex_cond() {
  int i;
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
}

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

  /*********************************************************************/
  /* CREATE SIGNAL HANDLER THREAD, PRODUCER AND CONSUMERS              */
  /*********************************************************************/

  if (pthread_create(&sig_wait_id, NULL, sig_waiter, NULL) != 0) {
    printf("pthread_create failed ");
    exit(3);
  }

  pthread_attr_init(&thread_attr);
  pthread_attr_setinheritsched(&thread_attr, PTHREAD_INHERIT_SCHED);

#ifdef GLOBAL
  sched_struct.sched_priority = sched_get_priority_max(SCHED_OTHER);
  pthread_attr_setinheritsched(&thread_attr, PTHREAD_EXPLICIT_SCHED);
  pthread_attr_setschedpolicy(&thread_attr, SCHED_OTHER);
  pthread_attr_setschedparam(&thread_attr, &sched_struct);
  pthread_attr_setscope(&thread_attr, PTHREAD_SCOPE_SYSTEM);
#endif  // GLOBAL

  if ( pthread_create (&thread_id[0], &thread_attr,
                       producer, NULL ) != 0 ) {
    printf ( "pthread_create failed " );
    exit ( 3 );
  }
  for ( i = 1; i < NUMCONSUMERS + 1; i++ ) {
    if ( pthread_create ( &thread_id [i], &thread_attr,
                          consumer, ( void * )&arg_array [i]) != 0 ){
      printf ( "pthread_create failed" );
      exit ( 3 );
    }
  }

  printf ( "just after threads created\n" );
    
  return 0;
}
