#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include "./donuts.h"

/******************************************************************************/
/* GLOBAL VARIABLES                                                           */
/******************************************************************************/
donut_ring_t    shared_ring;
pthread_mutex_t prod[MAXFLAVORS];
pthread_mutex_t cons[MAXFLAVORS];
pthread_cond_t  prod_cond[MAXFLAVORS];
pthread_cond_t  cons_cond[MAXFLAVORS];
pthread_t       thread_id[MAXCONSUMERS + MAXPRODUCERS];
pthread_t       sig_wait_id;

int main(/* int argc, char *argv[] */) {
  // TODO(rhennigan): set these by looping over test parameters
  int numflavors   = MAXFLAVORS;
  int numslots     = MAXSLOTS;
  int numconsumers = MAXCONSUMERS;
  int numproducers = MAXPRODUCERS;
  int numdozens    = MAXDOZENS;

  int nsigs;
  struct timeval first_time, last_time;
  struct sigaction new_act;
  // int arg_array[MAXCONSUMERS];
  cons_arg_t arg_array[MAXCONSUMERS];
  sigset_t all_signals;

  int sigs[] = { SIGBUS, SIGSEGV, SIGFPE };

  pthread_attr_t thread_attr;
  struct sched_param shed_struct;

  int i, j;

  /****************************************************************************/
  /* INITIAL TIMESTAMP VALUE FOR PERFORMANCE MEASURE                          */
  /****************************************************************************/

  for (i = 0; i < numconsumers + 1; i++) {
    /* SET ARRAY OF ARGUMENT VALUES */
    arg_array[i].id = i;
  }

  /****************************************************************************/
  /* GENERAL PTHREAD MUTEX AND CONDITION INIT AND GLOBAL INIT                 */
  /****************************************************************************/

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

  /****************************************************************************/
  /* SETUP FOR MANAGING THE SIGTERM SIGNAL, BLOCK ALL SIGNALS                 */
  /****************************************************************************/

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

  /****************************************************************************/
  /* CREATE SIGNAL HANDLER THREAD, PRODUCER AND CONSUMERS                     */
  /****************************************************************************/

  if (pthread_create(&sig_wait_id, NULL, sig_waiter, NULL) != 0) {
    printf("pthread_create failed ");
    exit(3);
  }

  pthread_attr_init(&thread_attr);
  pthread_attr_setinheritsched(&thread_attr, PTHREAD_INHERIT_SCHED);

# ifdef GLOBAL
  sched_struct.sched_priority = sched_get_priority_max(SCHED_OTHER);
  pthread_attr_setinheritsched(&thread_attr, PTHREAD_EXPLICIT_SCHED);
  pthread_attr_setschedpolicy(&thread_attr, SCHED_OTHER);
  pthread_attr_setschedparam(&thread_attr, &sched_struct);
  pthread_attr_setscope(&thread_attr, PTHREAD_SCOPE_SYSTEM);
# endif  // GLOBAL

  if (pthread_create(&thread_id[0], &thread_attr, producer, NULL) != 0) {
    printf("pthread_create failed ");
    exit(3);
  }
  for (i = 1; i < numconsumers + 1; i++) {
    if (pthread_create(&thread_id[i], &thread_attr, consumer,
      (void *)&arg_array[i]) != 0) {
      printf("pthread_create failed");
      exit(3);
    }
  }

  printf("just after threads created\n");

  /****************************************************************************/
  /* WAIT FOR ALL CONSUMERS TO FINISH, SIGNAL WAITER WILL                     */
  /* NOT FINISH UNLESS A SIGTERM ARRIVES AND WILL THEN EXIT                   */
  /* THE ENTIRE PROCESS....OTHERWISE MAIN THREAD WILL EXIT                    */
  /* THE PROCESS WHEN ALL CONSUMERS ARE FINISHED                              */
  /****************************************************************************/

  for (i = 1; i < numconsumers + 1; i++)
    pthread_join(thread_id[i], NULL);

  /****************************************************************************/
  /* GET FINAL TIMESTAMP, CALCULATE ELAPSED SEC AND USEC                      */
  /****************************************************************************/


  gettimeofday(&last_time, (struct timezone *)0);

  i = last_time.tv_sec - first_time.tv_sec;
  if (i == 0) {
    j = last_time.tv_usec - first_time.tv_usec;
  } else {
    if (last_time.tv_usec - first_time.tv_usec < 0) {
      i--;
      j = 1000000 + (last_time.tv_usec - first_time.tv_usec);
    } else {
      j = last_time.tv_usec - first_time.tv_usec;
    }
  }

  printf("Elapsed consumer time is %d sec and %d usec\n", i, j);

  printf("\n\n ALL CONSUMERS FINISHED, KILLING  PROCESS\n\n");
  exit(0);
}

/******************************************************************************/
/* PTHREAD PRODUCER ROUTINE...                                                */
/******************************************************************************/
void * producer(void * arg) {
  unsigned short xsub[3];
  struct timeval randtime;
  int sel;

  /* retrieve individual arguments */
  prod_arg_t * prod_arg = arg;
  int numslots = prod_arg->numslots;

  /* seed the random number generator */
  gettimeofday(&randtime, (struct timezone *)0);
  xsub[0] = (ushort)(randtime.tv_usec);
  xsub[1] = (ushort)(randtime.tv_usec >> 16);
  xsub[2] = (ushort)(pthread_self());

  while (1) {
    /* make a flavor selection */
    sel = nrand48(xsub) & 3;

    /* entering critical region; lock the mutex for this flavor */
    pthread_mutex_lock(&prod[sel]);

    /* if there's no room left in the buffer, thread will wait until signaled */
    while (shared_ring.spaces[sel] == 0) {
      pthread_cond_wait(&prod_cond[sel], &prod[sel]);
      /* consumer must signal prod_cond[sel] after freeing up a space */
    }
    /* increment the donut id for the selected flavor */
    shared_ring.serial[sel] += 1;

    /* insert a new donut */
    shared_ring.flavor[sel][shared_ring.in_ptr[sel]] = shared_ring.serial[sel];

    /* move in_ptr forward and cycle if necessary */
    shared_ring.in_ptr[sel] = (shared_ring.in_ptr[sel] + 1) % numslots;

    /* decrement the number of available spaces */
    shared_ring.spaces[sel] -= 1;

    /* increment the number of available donuts */
    shared_ring.donuts[sel] += 1;

    /* release our hold on the mutex for this flavor */
    pthread_mutex_unlock(&prod[sel]);

    /* signal cons_cond[sel] now that donuts are available */
    pthread_cond_signal(&cons_cond[sel]);
  }
  return NULL;
}

/******************************************************************************/
/* PTHREAD CONSUMER ROUTINE...                                                */
/******************************************************************************/
void * consumer(void * arg) {
  int dz, dn, sel;
  unsigned short xsub[3];
  struct timeval randtime;
  int collection[MAXDOZENS][12];

  /* retrieve individual arguments */
  cons_arg_t * cons_arg = arg;
  int numslots = cons_arg->numslots;  // number of slots in the ring buffer
  int numdozen = cons_arg->numdozen;  // number of dozens to collect

  /* seed the random number generator */
  gettimeofday(&randtime, (struct timezone *)0);
  xsub[0] = (ushort)(randtime.tv_usec);
  xsub[1] = (ushort)(randtime.tv_usec >> 16);
  xsub[2] = (ushort)(pthread_self());

  for (dz = 0; dz < numdozen; dz++) {  // for each dozen
    for (dn = 0; dn < 12; dn++) {  // for each donut
      /* make a flavor selection */
      sel = nrand48(xsub) & 3;

      /* entering critical region */
      pthread_mutex_lock(&cons[sel]);

      /* if there are no donuts available, thread will wait until signaled */
      while (shared_ring.donuts[sel] == 0) {
        pthread_cond_wait(&cons_cond[sel], &cons[sel]);
        /* producer must signal cons_cond[sel] when available */
      }

      /* remove a donut and add it to our collection */
      collection[dz][dn] = shared_ring.flavor[sel][shared_ring.outptr[sel]];
      shared_ring.flavor[sel][shared_ring.outptr[sel]] = 0;

      /* move outptr forward and cycle if necessary */
      shared_ring.outptr[sel] = (shared_ring.outptr[sel] + 1) % numslots;

      /* increment the number of available spaces */
      shared_ring.spaces[sel] += 1;

      /* decrement the number of available donuts */
      shared_ring.donuts[sel] -= 1;

      /* release our hold on the mutex for this flavor */
      pthread_mutex_unlock(&cons[sel]);

      /* signal prod_cond[sel] now that production space is available */
      pthread_cond_signal(&prod_cond[sel]);
    }

    /* sleep 1 ms to give other consumer threads a chance to run */
    usleep(1000);
  }

  /* record the results */
  output_collection(numdozen, collection);
  return NULL;
}

/******************************************************************************/
/* CONSUMER EXPORT RESULTS ROUTINE...                                         */
/******************************************************************************/
void output_collection(int N, int collection[N][12]) {
  int i, j;
  printf("results:\n");
  for (i = 0; i < N; i++) {
    for (j = 0; j < 12; j++) {
      printf(" %3d", collection[i][j]);
    }
    printf("\n");
  }
}

/******************************************************************************/
/* PTHREAD ASYNCH SIGNAL HANDLER ROUTINE...                                   */
/******************************************************************************/
void * sig_waiter(void * arg) {
  sigset_t sigterm_signal;
  int * signo = arg;

  sigemptyset(&sigterm_signal);
  sigaddset(&sigterm_signal, SIGTERM);
  sigaddset(&sigterm_signal, SIGINT);

  if (sigwait(&sigterm_signal, signo) != 0) {
    printf("\n  sigwait() failed, exiting\n");
    exit(2);
  }
  printf("process going down on SIGNAL (number %d)\n\n", *signo);
  exit(1);
  return NULL;
}

/******************************************************************************/
/* PTHREAD SYNCH SIGNAL HANDLER ROUTINE...                                    */
/******************************************************************************/
void sig_handler(int sig) {
  pthread_t signaled_thread_id;
  int i, thread_index;

  signaled_thread_id = pthread_self();
  for (i = 0; i < (numconsumers + 1); i++) {
    if (signaled_thread_id == thread_id[i]) {
      thread_index = i;
      break;
    }
  }
  printf("\nThread %d took signal # %d, PROCESS HALT\n", thread_index, sig);
  exit(1);
}
