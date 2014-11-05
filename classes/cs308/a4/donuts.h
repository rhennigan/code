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

/**********************************************************************/
/* SIGNAL WAITER, PRODUCER AND CONSUMER THREAD FUNCTIONS              */
/**********************************************************************/
void * sig_waiter(void * arg);
void * producer(void * arg);
void * consumer(void * arg);
void sig_handler(int sig_num);

#define _MD_ MAXDOZENS
#define _MF_ MAXFLAVORS
void output_collection(int id, donut_t collection[_MD_][_MF_][12 * _MF_]);
#undef _MD_
#undef _MF_

#endif  // DONUTS_H_
