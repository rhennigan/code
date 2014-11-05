#ifndef DONUTS_H_
#define DONUTS_H_

#include <signal.h>
#include <sys/time.h>
#include <pthread.h>

#define MAXFLAVORS   4
#define MAXSLOTS     50
#define MAXCONSUMERS 50
#define MAXPRODUCERS 30
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
typedef struct donut { int fl; int id; } donut_t;

/**********************************************************************/
/* SIGNAL WAITER, PRODUCER AND CONSUMER THREAD FUNCTIONS              */
/**********************************************************************/
void * sig_waiter(void * arg);
void * producer(void * arg);
void * consumer(void * arg);
void sig_handler(int sig_num);
void output_c(int id, donut_t c[MAXDOZENS][MAXFLAVORS][12 * MAXFLAVORS]);
long int elapsed(struct timeval *t2, struct timeval *t1);

#endif  // DONUTS_H_
