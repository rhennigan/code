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

  unsigned int i, j;
  for (i = 0; i < 5; i++) {
    assign_t * a = new_assign_prompt();
    pq_enqueue(pq, a);

    /* print current list */
    print_assignment_hdr();
#   ifdef _USE_HEAP_
    pq_sort(pq);
    for (j = 0; j < pq->sz_lst; j++) {
      print_assignment(pq->list[pq->sz_lst - j - 1]);
    }
#   else
    list_iter(pq->list, &print_assignment);
#   endif  // _USE_HEAP_
    printf("\n\n");
  }

  pq_dump(pq);
  pq_dispose(pq);
  return EXIT_SUCCESS;
}

bool compare(void * addr1, void * addr2) {
  assign_t * a1 = addr1;
  assign_t * a2 = addr2;
  /* printf("%s%s%d\t\t%d/%d\n", a1->course_name, a1->assign_name, */
  /*        a1->points, a1->due.month, a1->due.day); */
  int t1 = 31 * a1->due.month + a1->due.day;
  int t2 = 31 * a2->due.month + a2->due.day;
  /* printf("comparing (%d/%d, %d) with (%d/%d, %d)\n", */
  /*        a1->due.month, a1->due.day, a1->points, */
  /*        a2->due.month, a2->due.day, a2->points); */
  /* printf("  t1 = %d\n", t1); */
  /* printf("  t2 = %d\n", t2); */
  /* printf("  t1 < t2 = %d\n", (t1 < t2)); */
  /* printf("  t1 == t2 = %d\n", (t1 == t2)); */
  /* printf("  a1->points > a2->points = %d\n", (a1->points > a2->points)); */
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

  printf("%s%s%d\t\t%d/%d\n", cname, aname,
         a->points, a->due.month, a->due.day);
}

void print_assignment_hdr() {
  printf("\nCourse");
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
  printf("enter the course name: ");
  char * cname = get_input_string();

  printf("enter the assignment name: ");
  char * aname = get_input_string();

  printf("enter the number of points: ");
  int pts = get_input_int(0, INT_MAX);

  printf("enter the month of the due date (1-12): ");
  int m = get_input_int(1, 12);

  printf("enter the day of the due date (1-31): ");
  int d = get_input_int(1, 31);

  return new_assign(cname, aname, pts, m, d);
}


