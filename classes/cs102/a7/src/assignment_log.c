// assignment_log.c
// Copyright (C) 2014 Richard Hennigan

#define _USE_HEAP_

#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include "../lib/list.h"
#include "../lib/user_input.h"

#ifdef _USE_HEAP_
#include "../lib/pq_heap.h"
#else
#include "../lib/pq.h"
#endif  // _USE_HEAP_

#define STR_SZ 30

typedef struct ddate_s {
  int month;
  int day;
} ddate_t;

typedef struct assign_s {
  char course_name[STR_SZ];
  char assign_name[STR_SZ];
  int points;
  ddate_t due;
} assign_t;

#define _SWAP(a, b) do {                        \
    register void * t = (a);                    \
    (a) = (b);                                  \
    (b) = t;                                    \
  } while (0);

bool compare(void * addr1, void * addr2);
void print_assignment(void * addr);
void print_assignment_hdr();
assign_t * new_assign(char * cname, char * aname, int points, int m, int d);
assign_t * new_assign_prompt();


int main() {
  pq_t * pq = pq_init(sizeof(assign_t), &compare);
  vskip(24);

  unsigned int i, j;
  for (i = 0; i < 5; i++) {
    assign_t * a = new_assign_prompt();
    vskip(5);
    pq_enqueue(pq, a);

    /* print current list */
    print_assignment_hdr();
#ifdef _USE_HEAP_
    pq_sort(pq);
    for (j = 0; j < pq->sz_lst; j++) {
      print_assignment(pq->list[j /* pq->sz_lst - j - 1 */]);
    }
#else
    list_iter(pq->list, &print_assignment);
#endif  // _USE_HEAP_
    repeat('-', 80);
    printf("\n\n");
    WAIT();
    vskip(24);
  }

  for (i = 0; i < 2; i++) {
    assign_t * next = pq_peek(pq);
    printf("NEXT ASSIGNMENT:\n");
    printf(" course:     %s\n", next->course_name);
    printf(" assignment: %s\n", next->assign_name);
    printf(" points:     %d\n", next->points);
    printf(" due:        %d/%d\n", next->due.month, next->due.day);
    printf("\nPress enter when the assignment is complete\n");
    WAIT();
    pq_dequeue(pq);
    vskip(24);
  }

  /* print current list */
  print_assignment_hdr();
#ifdef _USE_HEAP_
  pq_sort(pq);
  for (j = 0; j < pq->sz_lst; j++) {
    print_assignment(pq->list[j]);
  }
#else
  list_iter(pq->list, &print_assignment);
#endif  // _USE_HEAP_
  repeat('-', 80);
  printf("\n\n");

  pq_dump(pq);
  pq_dispose(pq);
  return EXIT_SUCCESS;
}

bool compare(void * addr1, void * addr2) {
  assign_t * a1 = addr1;
  assign_t * a2 = addr2;
  int t1 = 31 * a1->due.month + a1->due.day;
  int t2 = 31 * a2->due.month + a2->due.day;
  if (t1 < t2) {
    return true;
  } else if (t1 == t2) {
    return (a1->points > a2->points);
  } else {
    return false;
  }
}

void print_assignment(void * addr) {
  assign_t * a = addr;
  char cname[STR_SZ];
  char aname[STR_SZ];
  int i;
  for (i = 0; i < STR_SZ; i++) {
    if (a->course_name[i] == '\0') {
      for (; i < STR_SZ - 1; i++) {
        cname[i] = ' ';
      }
      break;
    }
    cname[i] = a->course_name[i];
  }
  cname[STR_SZ - 1] = '\0';

  for (i = 0; i < STR_SZ; i++) {
    if (a->assign_name[i] == '\0') {
      for (; i < STR_SZ - 1; i++) {
        aname[i] = ' ';
      }
      break;
    }
    aname[i] = a->assign_name[i];
  }
  aname[STR_SZ - 1] = '\0';

  printf(" %s%s%d\t\t%d/%d\n", cname, aname,
         a->points, a->due.month, a->due.day);
}

void print_assignment_hdr() {
  printf("CURRENT ASSIGNMENTS\n");
  repeat('-', 80);
  printf("\n");
  printf(" Course");
  hskip(STR_SZ - 7);
  printf("Assignment");
  hskip(STR_SZ - 11);
  printf("Points\tDue\n");
  repeat('-', 80);
  printf("\n");
}

assign_t * new_assign(char * cname, char * aname, int points, int m, int d) {
  assign_t * a = malloc(sizeof(assign_t));
  snprintf(a->course_name, STR_SZ, "%s", cname);
  snprintf(a->assign_name, STR_SZ, "%s", aname);
  a->points = points;
  ddate_t due;
  due.month = m;
  due.day = d;
  a->due = due;
  return a;
}

assign_t * new_assign_prompt() {
  printf("ENTER A NEW ASSIGNMENT\n");
  repeat('-', 80);
  printf("\n");
  printf(" enter the course name: ");
  char * cname = get_input_string();

  printf(" enter the assignment name: ");
  char * aname = get_input_string();

  printf(" enter the number of points: ");
  int pts = get_input_int(0, INT_MAX);

  printf(" enter the month of the due date (1-12): ");
  int m = get_input_int(1, 12);

  printf(" enter the day of the due date (1-31): ");
  int d = get_input_int(1, 31);

  repeat('-', 80);
  return new_assign(cname, aname, pts, m, d);
}


