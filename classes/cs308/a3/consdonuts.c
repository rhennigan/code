#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <unistd.h>
#include <time.h>
#include <sys/time.h>
#include "./donuts.h"

#define _DEBUG_

// #define _USE_COLOR_TERM_

#ifdef _USE_COLOR_TERM_
#define C_DEF "\033[0m"
#define C_BLD "\033[1m\033[37m"
#else
#define C_DEF ""
#define C_BLD ""
#endif

typedef struct donut_s {
  int flavor;
  int num;
} donut_t;

int shmid, semid[3];

int p(int semidgroup, int donut_type);
int v(int semidgroup, int donut_type);
void print_donut_ring(donut_ring_t ring, int numslots);
void initialize_semaphores();
int sem_inspect(int semidgroup, int donut_type);
void display_sem_contents(char name[], int sem_id, donut_ring_t ring,
                          int numslots);
void create_seed(ushort seed[3]);
donut_t consume_donut(ushort seed[3], donut_ring_t ring, int numslots);
void consume_report(int dozens, ushort seed[3], donut_ring_t shared_ring,
                    int numslots);
void touch_update();
donut_ring_t get_shared_ring();

int main(int argc, char *argv[]) {
  assert(argc == 4);
  int consumer_number = atoi(argv[1]);
  int numslots = atoi(argv[2]);
  int dozens = atoi(argv[3]);

  ushort seed[3];
  create_seed(seed);
  initialize_semaphores();
  donut_ring_t shared_ring = get_shared_ring();
  consume_report(dozens, seed, shared_ring, numslots);
  fflush(NULL);

  return 0;
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

donut_t consume_donut(ushort seed[3], donut_ring_t ring, int numslots) {
  int donut_type = nrand48(seed) & 3;
  p(semid[CONSUMER], donut_type);  // wait until ready
  p(semid[OUTPTR], donut_type);  // enter critical region
  int ptr = ring->outptr[donut_type];
  int donut_num = ring->flavor[donut_type][ptr];
  ring->flavor[donut_type][ptr] = 0;
  ring->outptr[donut_type] = (ring->outptr[donut_type] + 1) % numslots;
  v(semid[OUTPTR], donut_type);  // exit critical region
  v(semid[PROD], donut_type);
  donut_t donut = {donut_type, donut_num};
  return donut;
}

void touch_update() {
  system("touch ./.conslk");
}

void consume_report(int dozens, ushort seed[3], donut_ring_t shared_ring,
                    int numslots) {
  pid_t pid = getpid();
  time_t timer;
  char t_str[80];
  struct tm* tm_info;
  time(&timer);
  tm_info = localtime(&timer);
  strftime(t_str, 80, "%T", tm_info);
  struct timeval ms;
  gettimeofday(&ms, NULL);
  char time_string[80];
  snprintf(time_string, sizeof(time_string), "%s.%d",
           t_str, (int)ms.tv_usec / 1000);

  donut_t donuts[NUMFLAVORS][12 * dozens];
  int ins_ptr[NUMFLAVORS];

  int i, j;
  int dozen;
  for (dozen = 0; dozen < dozens; dozen++) {
    for (i = 0; i < NUMFLAVORS; i++) {
      ins_ptr[i] = 0;
      for (j = 0; j < 12 * dozens; j++) {
        donuts[i][j] = (donut_t){0, 0};
      }
    }
    int donut_num;
    for (donut_num = 0; donut_num < 12; donut_num++) {
      donut_t new_donut = consume_donut(seed, shared_ring, numslots);
      touch_update();
      donuts[new_donut.flavor][ins_ptr[new_donut.flavor]] = new_donut;
      ins_ptr[new_donut.flavor] += 1;
    }

#ifdef _DEBUG_
    printf("\n----------------------------------------------------------\n");
    printf(C_DEF "process PID: " C_BLD "%d\t", pid);
    printf(C_DEF "time: " C_BLD "%s\t", time_string);
    printf(C_DEF "dozen #: " C_BLD "%d\n", dozen + 1);
    printf("" C_DEF "\n");

    printf("plain\t\tjelly\t\tcoconut\t\thoney-dip");
    printf("\n" C_BLD "");

    int flav, row = 0, done = 0;
    while (!done) {
      done = 1;
      for (flav = 0; flav < NUMFLAVORS; flav++) {
        if (donuts[flav][row].num) {
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
  }
}

donut_ring_t get_shared_ring() {
  donut_ring_t shared_ring;
  int flags = 0666 | IPC_CREAT;
  if ((shmid = shmget(MEMKEY, sizeof(struct donut_ring), flags)) == -1) {
    perror("shared get failed: ");
    exit(EXIT_FAILURE);
  }
  if ((shared_ring =
       (donut_ring_t)shmat(shmid, NULL, 0)) == (void *)(-1)) {
    perror("shared attach failed: ");
    exit(EXIT_FAILURE);
  }
  return shared_ring;
}
