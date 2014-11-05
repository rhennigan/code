#ifndef DONUTS_H_
#define DONUTS_H_

#include <signal.h>
#include <sys/time.h>
#include <pthread.h>

#define MAXFLAVORS   4
#define MAXSLOTS     50
#define MAXCONSUMERS 5
#define MAXPRODUCERS 5
#define MAXDOZENS    5

struct donut_ring {
  int flavor[MAXFLAVORS][MAXSLOTS];
  int outptr[MAXFLAVORS];
  int in_ptr[MAXFLAVORS];
  int serial[MAXFLAVORS];
  int spaces[MAXFLAVORS];
  int donuts[MAXFLAVORS];
};

typedef struct donut_ring donut_ring_t;

/**********************************************************************/
/* SIGNAL WAITER, PRODUCER AND CONSUMER THREAD FUNCTIONS              */
/**********************************************************************/
void * sig_waiter(void * arg);
void * producer(void * arg);
void * consumer(void * arg);
void   sig_handler(int sig_num);
void   output_collection(int N, int collection[N][12]);

/**********************************************************************/
/* PTHREAD ROUTINE ARGUMENT STRUCTS                                   */
/**********************************************************************/
typedef struct prod_arg {
  int id;        // id number of producer thread
  int numslots;  // number of slots in the ring buffer
} prod_arg_t;

typedef struct cons_arg {
  int id;        // id number of consumer thread
  int numslots;  // number of slots in the ring buffer
  int numdozen;  // number of dozens to collect
} cons_arg_t;

#endif  // DONUTS_H_
