// test.c
// Copyright (C) 2014 Richard Hennigan

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lib/list.h"
#include "lib/pq.h"

#define STR_SZ 64

typedef struct date_s {
  int month;
  int day;
} date_t;

typedef struct assign_s {
  char course_name[STR_SZ];
  char assign_name[STR_SZ];
  int points;
  date_t due;
} assign_t;

bool compare(void * addr1, void * addr2);
void print_assignment(void * addr);
assign_t * new_assign(char * cname, char * aname, int points, date_t due);
assign_t * new_assign_prompt();

assign_t * new_assign_prompt();


int main() {
  pq_t * pq = pq_init(sizeof(assign_t), &compare);

  assign_t * a1 = new_assign("course 1", "paper", 25, (date_t){11, 5});
  assign_t * a2 = new_assign("course 2", "project", 15, (date_t){11, 5});

  pq_enqueue(pq, a1);
  pq_enqueue(pq, a2);

  list_iter(pq->list, &print_assignment);
  printf("\n\n");

  pq_dump(pq);

  pq_dispose(pq);

  return 0;
}

bool compare(void * addr1, void * addr2) {
  assign_t * a1 = addr1;
  assign_t * a2 = addr2;
  int t1 = 31 * a1->due.month + a1->due.day;
  int t2 = 31 * a2->due.month + a2->due.day;
  if (t1 < t2) {
    return true;
  } else if (t1 == t2 && a1->points > a2->points) {
    return true;
  } else {
    return false;
  }
}

void print_assignment(void * addr) {
  assign_t * a = addr;
  printf("assignment:\n");
  printf("----------------------------\n");
  printf("  course:     %s\n", a->course_name);
  printf("  assignment: %s\n", a->assign_name);
  printf("  points      %d\n", a->points);
  printf("  due         %d / %d\n", a->due.month, a->due.day);
  printf("\n");
}

assign_t * new_assign(char * cname, char * aname, int points, date_t due) {
  assign_t * a = malloc(sizeof(assign_t));
  snprintf(a->course_name, STR_SZ, "%s", cname);
  snprintf(a->assign_name, STR_SZ, "%s", aname);
  a->points = points;
  a->due = due;
  return a;
}
