#include "./donuts.h"

donut_ring_t shared_ring;
pthread_mutex_t prod[MAXFLAVORS];
pthread_mutex_t cons[MAXFLAVORS];
pthread_cond_t prod_cond[MAXFLAVORS];
pthread_cond_t cons_cond[MAXFLAVORS];
pthread_t thread_id[MAXCONSUMERS + MAXPRODUCERS];
pthread_t sig_wait_id;

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
  for ( i = 0; i < NUMCONSUMERS + 1; i++ ) {
    arg_array [i] = i;	/** SET ARRAY OF ARGUMENT VALUES **/
  }

  return 0;
}
