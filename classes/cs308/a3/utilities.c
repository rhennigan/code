#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>
#include <unistd.h>
#include <sys/sem.h>
#include "./donuts.h"

int p(int semidgroup, int donut_type) {
  struct sembuf semopbuf;
  semopbuf.sem_num = donut_type;
  semopbuf.sem_op = (-1);
  semopbuf.sem_flg = 0;
  if (semop(semidgroup, &semopbuf, 1) == -1) {
    return -1;
  }
  return 0;
}

int v(int semidgroup, int donut_type) {
  struct sembuf semopbuf;
  semopbuf.sem_num = donut_type;
  semopbuf.sem_op = (+1);
  semopbuf.sem_flg = 0;
  if (semop(semidgroup, &semopbuf, 1) == -1) {
    return -1;
  }
  return 0;
}

int semsetall(int semgroup, int number_in_group, int set_all_value) {
  int i, j, k;

#ifdef _SEM_SEMUN_UNDEFINED
  union semun {
    int val;
    struct semid_ds *buf;
    unsigned short int *array;
  } sem_ctl_un;
#endif

  sem_ctl_un.val = set_all_value;
  for (i = 0; i < number_in_group; i++) {
    if (semctl(semgroup, i, SETVAL, sem_ctl_un) == -1) {
      return (-1);
    }
  }
  return (0);
}

int sem_inspect(int semidgroup, int donut_type) {
  int sem_value;
  if ((sem_value = semctl(semidgroup, donut_type, GETVAL, 0)) == -1) {
    perror("semctl: GETVAL");
    exit(EXIT_FAILURE);
  }
  return sem_value;
}

void display_sem_contents(char name[], int sem_id, donut_ring_t ring,
                          int numslots) {
  int donut_type;
  printf("\n---------------------------\n");
  printf(" SEMAPHORE [%s] CONTENTS", name);
  printf("\n---------------------------\n");
  for (donut_type = 0; donut_type < NUMFLAVORS; donut_type++) {
    int val = sem_inspect(sem_id, donut_type);
    printf("flav %d = %d,\tring contents: [", donut_type, val);
    int slot, empty = 1;
    for (slot = 0; slot < numslots; slot++) {
      if (ring->flavor[donut_type][slot] != 0) {
        printf("%d,", ring->flavor[donut_type][slot]);
        empty = 0;
      }
    }
    printf(empty ? " ]\n" : "\b]\n");
  }
}

void create_seed(ushort xsub1[3]) {
  struct timeval randtime;
  gettimeofday(&randtime, (struct timezone *)0);
  xsub1[0] = (ushort)(randtime.tv_usec);
  xsub1[1] = (ushort)(randtime.tv_usec >> 16);
  xsub1[2] = (ushort)(getpid());
}
