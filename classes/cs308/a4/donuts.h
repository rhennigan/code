#ifndef DONUTS_H_
#define DONUTS_H_

#include <signal.h>
#include <sys/time.h>
#include <pthread.h>

#define MAXFLAVORS         4
#define MAXSLOTS           10000
#define MAXCONSUMERS       100
#define MAXPRODUCERS       100
#define MAXDOZENS          300
#define DEADLOCK_THRESHOLD 100000
#define TIME_KEEPER_PER    10000

struct donut_ring {
  int flavor[MAXFLAVORS][MAXSLOTS];
  int outptr[MAXFLAVORS];
  int in_ptr[MAXFLAVORS];
  int serial[MAXFLAVORS];
  int spaces[MAXFLAVORS];
  int donuts[MAXFLAVORS];
};

typedef struct donut_ring donut_ring_t;
typedef struct donut { int fl; int id; } donut_t;

/**********************************************************************/
/* SIGNAL WAITER, PRODUCER AND CONSUMER THREAD FUNCTIONS              */
/**********************************************************************/
void * sig_waiter(void * arg);
void * producer(void * arg);
void * consumer(void * arg);
void * time_keeper(void * arg);
void sig_handler(int sig_num);
void output_c(int id, donut_t c[MAXDOZENS][MAXFLAVORS][12 * MAXFLAVORS]);
void check_in(int tid);
long int elapsed_us(struct timeval *t2, struct timeval *t1);
long int last_check_in();

#endif  // DONUTS_H_
