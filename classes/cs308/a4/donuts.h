#ifndef DONUTS_H_
#define DONUTS_H_

#include <signal.h>
#include <sys/time.h>
#include <pthread.h>

#define MAXFLAVORS   4
#define MAXSLOTS     50
#define MAXCONSUMERS 1
#define MAXPRODUCERS 1
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
typedef donut_t donut_collection[MAXFLAVORS];

/**********************************************************************/
/* SIGNAL WAITER, PRODUCER AND CONSUMER THREAD FUNCTIONS              */
/**********************************************************************/
void * sig_waiter(void * arg);
void * producer(void * arg);
void * consumer(void * arg);
void sig_handler(int sig_num);
void output_collection(int id, donut_t collection[MAXFLAVORS][12 * MAXDOZENS]);

#endif  // DONUTS_H_
