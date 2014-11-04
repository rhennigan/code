#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <math.h>

#define NTHREADS 8

void * print_hello_world(void * tid) {
  int * id = tid;
  double val = 0.0;
  long int i;
  for (i = 1; i < 10000000000; i++) {
    val += 1.0 / (double)i;
  }

  printf("Thread #%d reults: val = %f\n", *id, val);
  pthread_exit(NULL);
}

int main(int argc, char *argv[]) {
  pthread_t threads[NTHREADS];
  int thr_id[NTHREADS];
  int status, i;

  for (i = 0; i < NTHREADS; i++) {
    printf("Initializing thread #%d\n", i);
    thr_id[i] = i;
    status = pthread_create(&threads[i], NULL, print_hello_world, thr_id + i);

    if (status != 0) {
      printf("pthread error %d\n", status);
      exit(EXIT_FAILURE);
    }
  }

  sleep(3);
  exit(EXIT_SUCCESS);
}

