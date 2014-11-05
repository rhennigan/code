#include <stdlib.h>
#include <stdio.h>
#include <unistd.h>
#include <time.h>
#include "./donuts.h"

#define _DEBUG_

#define _USE_COLOR_TERM_

#ifdef _USE_COLOR_TERM_
#define C_DEF "\033[0m"
#define C_BLD "\033[1m\033[37m"
#else
#define C_DEF ""
#define C_BLD ""
#endif

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
int             numflavors;
int             numslots;
int             numconsumers;
int             numproducers;
int             numdozen;

int timeval_subtract(struct timeval * result,
                     struct timeval * last,
                     struct timeval * first);

int main(/* int argc, char *argv[] */) {
  // TODO(rhennigan): set these by looping over test parameters
  numflavors   = MAXFLAVORS;
  numslots     = MAXSLOTS;
  numconsumers = MAXCONSUMERS;
  numproducers = MAXPRODUCERS;
  numdozen     = MAXDOZENS;

  struct timeval first_time, last_time;

  int arg_array[MAXCONSUMERS];

  pthread_attr_t th_attr;
  struct sched_param shed_struct;

  int i, j;

  /****************************************************************************/
  /* INITIAL TIMESTAMP VALUE FOR PERFORMANCE MEASURE                          */
  /****************************************************************************/
  gettimeofday(&first_time, (struct timezone *)0);
  for (i = 0; i < numconsumers + 1; i++) {
    arg_array[i] = i;  // SET ARRAY OF ARGUMENT VALUES
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
  sigset_t all_signals;
  int sigs[] = { SIGBUS, SIGSEGV, SIGFPE };
  int nsigs = sizeof(sigs) / sizeof(int);
  struct sigaction new_act;

  /* create signal set with all signals but SIGBUS, SIGSEGV, and SIGFPE */
  sigfillset(&all_signals);
  for (i = 0; i < nsigs; i++) {
    sigdelset(&all_signals, sigs[i]);
  }

  /* block everything remaining in all_signals */
  sigprocmask(SIG_BLOCK, &all_signals, NULL);

  /* initialize all_signals */
  sigfillset(&all_signals);
  for (i = 0; i < nsigs; i++) {
    new_act.sa_handler = sig_handler;
    new_act.sa_mask    = all_signals;
    new_act.sa_flags   = 0;
    if (sigaction(sigs[i], &new_act, NULL) == -1) {
      perror("can't set signals: ");
      exit(EXIT_FAILURE);
    }
  }

  printf("just before threads created\n");

  /****************************************************************************/
  /* CREATE SIGNAL HANDLER THREAD, PRODUCER AND CONSUMERS                     */
  /****************************************************************************/

  /* pthread_create(pthread_t * thread, const pthread_attr_t * attr,
                    void *(*start_routine) (void *), void * arg)      */
  if (pthread_create(&sig_wait_id, NULL, sig_waiter, NULL) != 0) {
    printf("pthread_create failed ");
    exit(3);
  }

  pthread_attr_init(&th_attr);
  pthread_attr_setinheritsched(&th_attr, PTHREAD_INHERIT_SCHED);

#ifdef GLOBAL
  sched_struct.sched_priority = sched_get_priority_max(SCHED_OTHER);
  pthread_attr_setinheritsched(&th_attr, PTHREAD_EXPLICIT_SCHED);
  pthread_attr_setschedpolicy(&th_attr, SCHED_OTHER);
  pthread_attr_setschedparam(&th_attr, &sched_struct);
  pthread_attr_setscope(&th_attr, PTHREAD_SCOPE_SYSTEM);
#endif  // GLOBAL

  /* create all the producer threads */
  for (i = 0; i < numproducers; i++) {
    if (pthread_create(&thread_id[i], &th_attr, producer, NULL) != 0) {
      printf("pthread_create failed ");
      exit(3);
    }
  }

  /* create all the consumer threads */
  for (i = numproducers; i < numconsumers + numproducers; i++) {
    if (pthread_create(&thread_id[i], &th_attr, consumer,
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

  for (i = numproducers; i < numconsumers + numproducers; i++)
    pthread_join(thread_id[i], NULL);

  /****************************************************************************/
  /* GET FINAL TIMESTAMP, CALCULATE ELAPSED SEC AND USEC                      */
  /****************************************************************************/
  gettimeofday(&last_time, (struct timezone *)0);
  /* struct timeval elapsed; */
  /* timeval_subtract(&elapsed, &last_time, &first_time); */
  /* long int sec = elapsed.tv_sec; */
  /* long int usec = elapsed.tv_usec; */
  long int sec, usec;
  if ((sec = last_time.tv_sec - first_time.tv_sec) == 0) {
    usec = last_time.tv_usec - first_time.tv_usec;
  } else {
    if (last_time.tv_usec - first_time.tv_usec < 0) {
      sec--;
      usec = 1000000 + (last_time.tv_usec - first_time.tv_usec);
    } else {
      usec = last_time.tv_usec - first_time.tv_usec;
    }
  }

  printf("Elapsed consumer time is %ld sec and %ld usec\n", sec, usec);

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
  donut_t collection[MAXFLAVORS][12 * MAXDOZENS];
  int c_ptr[MAXFLAVORS];

  /* initialize the collection to zero */
  int i, j;
  for (i = 0; i < MAXFLAVORS; i++) {
    for (j = 0; j < 12 * MAXDOZENS; j++) {
      collection[i][j] = (donut_t){ -1, 0 };
    }
  }

  /* get thread id */
  int id = *(int *)arg;

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
      int d_id = shared_ring.flavor[sel][shared_ring.outptr[sel]];
      collection[sel][c_ptr[sel]++].id = d_id;
      collection[dz][dn].id = shared_ring.flavor[sel][shared_ring.outptr[sel]];
      collection[dz][dn].fl = sel;
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
  output_collection(id, collection);
  return NULL;
}

/******************************************************************************/
/* CONSUMER EXPORT RESULTS ROUTINE...                                         */
/******************************************************************************/
void output_collection(int id, donut_t collection[N][12]) {
  system("mkdir -p log/");

  time_t timer;
  char t_str[80];
  char time_string[80];
  struct tm tm_info;
  struct timeval ms;

  time(&timer);
  localtime_r(&timer, &tm_info);
  strftime(t_str, 80, "%T", &tm_info);
  gettimeofday(&ms, NULL);
  snprintf(time_string, sizeof(time_string), "%s.%d",
           t_str, (int)ms.tv_usec / 1000);

  int dozen;
  for (dozen = 0; dozen < numdozen; dozen++) {
#ifdef _DEBUG_
    printf("\n----------------------------------------------------------\n");
    printf(C_DEF "thread ID: " C_BLD "%d\t", id);
    printf(C_DEF "time: " C_BLD "%s\t", time_string);
    printf(C_DEF "dozen #: " C_BLD "%d\n", dozen + 1);
    printf("" C_DEF "\n");

    printf("plain\t\tjelly\t\tcoconut\t\thoney-dip");
    printf("\n" C_BLD "");

    int flav, row = 0, done = 0;
    while (!done) {
      done = 1;
      for (flav = 0; flav < numflavors; flav++) {
        if (collection[dozen][row].num) {
          printf("  %d\t\t", donuts[flav][row].num);
          done = 0;
        } else {
          printf("\t\t");
        }
      }
      row += 1;
      printf("\n" C_DEF "");
    }
    /* display_sem_contents("CONS", semid[CONSUMER], shared_ring, numslots); */
#endif

  int i, j, k = 0;
  printf("consumer %d results:\n", id);
  for (i = 0; i < N; i++) {
    printf(" dozen number: %d\n", i);
    for (k = 0; k < numflavors; k++) {
      printf("  flavor %d: ", k);
      for (j = 0; j < 12; j++) {
        if (collection[i][j].fl == k) {
          printf(" %3d", collection[i][j].id);
        }
      }
      printf("\n");
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

/* timeval_subtract from:
   www.gnu.org/software/libc/manual/html_node/Elapsed-Time.html */
int timeval_subtract(result, x, y)
    struct timeval *result, *x, *y;
{
  /* Perform the carry for the later subtraction by updating y. */
  if (x->tv_usec < y->tv_usec) {
    int nsec = (y->tv_usec - x->tv_usec) / 1000000 + 1;
    y->tv_usec -= 1000000 * nsec;
    y->tv_sec += nsec;
  }
  if (x->tv_usec - y->tv_usec > 1000000) {
    int nsec = (x->tv_usec - y->tv_usec) / 1000000;
    y->tv_usec += 1000000 * nsec;
    y->tv_sec -= nsec;
  }

  /* Compute the time remaining to wait.
     tv_usec is certainly positive. */
  result->tv_sec = x->tv_sec - y->tv_sec;
  result->tv_usec = x->tv_usec - y->tv_usec;

  /* Return 1 if result is negative. */
  return x->tv_sec < y->tv_sec;
}
