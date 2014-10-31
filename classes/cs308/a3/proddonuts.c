#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include <unistd.h>
#include <assert.h>
#include "./donuts.h"

#define _DEBUG_

int shmid, semid[3];

int p(int semidgroup, int donut_type);
int v(int semidgroup, int donut_type);
int semsetall(int semgroup, int number_in_group, int set_all_value);
int sem_inspect(int semidgroup, int donut_type);
void display_sem_contents(char name[], int sem_id, donut_ring_t ring,
                          int numslots);

void semsetallfull(int numslots);
void sig_handler(int sig_num);
void initialize_semaphores();
void initialize_sig_handler();
donut_ring_t initialize_shared_mem();
void create_seed(ushort xsub1[3]);
void print_donut_ring(donut_ring_t ring, int numslots);
void produce_donut(ushort seed[3], donut_ring_t ring, int ptr[], int seq[],
                   int numslots);
void touch_update();



int main(int argc, char *argv[]) {
  assert(argc == 2);
  int numslots = atoi(argv[1]);

  int in_ptr[NUMFLAVORS], serial[NUMFLAVORS];
  ushort xsub1[3];
  int i;
  for (i = 0; i < NUMFLAVORS; i++) {
    in_ptr[i] = 0;
    serial[i] = 0;
  }

  initialize_semaphores();
  printf("semid[PROD]     = %d\n", semid[PROD]);
  printf("semid[CONSUMER] = %d\n", semid[CONSUMER]);
  printf("semid[OUTPTR]   = %d\n", semid[OUTPTR]);

  initialize_sig_handler();
  donut_ring_t shared_ring = initialize_shared_mem();
  printf("shmid = %d\n", shmid);
  create_seed(xsub1);
  semsetallfull(numslots);

  while (1) {
    produce_donut(xsub1, shared_ring, in_ptr, serial, numslots);
    fflush(NULL);
    touch_update();
    #ifdef _DEBUG_
    display_sem_contents("PROD", semid[PROD], shared_ring, numslots);
    fflush(NULL);
    display_sem_contents("CONS", semid[CONSUMER], shared_ring, numslots);
    fflush(NULL);
    #endif
  }

  exit(EXIT_SUCCESS);
}



void semsetallfull(int numslots) {
  if (semsetall(semid[PROD], NUMFLAVORS, numslots) == -1) {
    perror("semsetall PROD failed: ");
    sig_handler(-1);
  }

  if (semsetall(semid[CONSUMER], NUMFLAVORS, 0) == -1) {
    perror("semsetall CONSUMER failed: ");
    sig_handler(-1);
  }

  if (semsetall(semid[OUTPTR], NUMFLAVORS, 1) == -1) {
    perror("semsetall OUTPTR failed: ");
    sig_handler(-1);
  }
}

void initialize_semaphores() {
  int flags = 0666 | IPC_CREAT;

  if ((semid[PROD] = semget(SEMKEY + 1, NUMFLAVORS, flags)) == -1) {
    perror("semget: semget (PROD) failed");
    exit(EXIT_FAILURE);
  }

  if ((semid[CONSUMER] = semget(SEMKEY + 2, NUMFLAVORS, flags)) == -1) {
    perror("semget: semget (CONSUMER) failed");
    exit(EXIT_FAILURE);
  }

  if ((semid[OUTPTR] = semget(SEMKEY + 3, NUMFLAVORS, flags)) == -1) {
    perror("semget: semget (OUTPTR) failed");
    exit(EXIT_FAILURE);
  }
}

void sig_handler(int sig_num) {
  int i;
  printf("In signal handler with signal # %d\n", sig_num);
  if (shmctl(shmid, IPC_RMID, 0) == -1) {
    perror("handler failed shm RMID: ");
  }
  for (i = 0; i < NUMSEMIDS; i++) {
    if (semctl(semid[i], 0, IPC_RMID, NULL) == -1) {
      perror("handler failed sem RMID: ");
    }
  }
  exit(5);
}

void initialize_sig_handler() {
  struct sigaction new;
  sigset_t mask_sigs;
  int sigs[] = { SIGHUP, SIGINT, SIGQUIT, SIGBUS, SIGTERM, SIGSEGV, SIGFPE };
  int nsigs  = sizeof(sigs) / sizeof(int);
  sigemptyset(&mask_sigs);
  int i;
  for (i = 0; i < nsigs; i++) {
    sigaddset(&mask_sigs, sigs[i]);
  }
  for (i = 0; i < nsigs; i++) {
    new.sa_handler = sig_handler;
    new.sa_mask    = mask_sigs;
    new.sa_flags   = 0;
    if (sigaction(sigs[i], &new, NULL) == -1) {
      perror("can't set signals: ");
      exit(EXIT_FAILURE);
    }
  }
}

donut_ring_t initialize_shared_mem(int numslots) {
  int i, j, flags = 0600 | IPC_CREAT;
  struct donut_ring * shared_ring;

  if ((shmid = shmget(MEMKEY, sizeof(struct donut_ring), flags)) == -1) {
    perror("shared get failed: ");
    exit(EXIT_FAILURE);
  }

  if ((shared_ring =
       (donut_ring_t)shmat(shmid, NULL, 0)) == (void *)(-1)) {
    perror("shared attach failed: ");
    exit(EXIT_FAILURE);
  }
  for (i = 0; i < NUMFLAVORS; i++) {
    for (j = 0; j < numslots; j++) {
      shared_ring->flavor[i][j] = 0;
    }
  }

  for (i = 0; i < NUMSEMIDS; i++) {
    if ((semid[i] == semget(SEMKEY + i, NUMFLAVORS, flags)) == -1) {
      perror("semaphore allocation failed: ");
      sig_handler(-1);
    }
  }
  return shared_ring;
}

void produce_donut(ushort seed[3], donut_ring_t ring, int ptr[], int seq[],
                   int numslots) {
  int donut_type = nrand48(seed) & 3;
  p(semid[PROD], donut_type);
  seq[donut_type] += 1;
  ring->flavor[donut_type][ptr[donut_type]] = seq[donut_type];
  ptr[donut_type] = (ptr[donut_type] + 1) % numslots;
  v(semid[CONSUMER], donut_type);
}

void print_donut_ring(donut_ring_t ring, int numslots) {
  int donut_type, slot = 0;
  for (donut_type = 0; donut_type < NUMFLAVORS; donut_type++) {
    printf("flavor %d = [", donut_type);
    int empty = 1;
    for (slot = 0; slot < numslots; slot++) {
      if (ring->flavor[donut_type][slot] != 0) {
        printf("%d,", ring->flavor[donut_type][slot]);
        empty = 0;
      }
    }
    printf(empty ? " ]\n" : "\b]\n");
  }
  printf("\n");
  fflush(stdout);
}

void touch_update() {
  system("touch ./.prodlk");
}
