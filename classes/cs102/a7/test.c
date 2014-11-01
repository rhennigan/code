// test.c
// Copyright (C) 2014 Richard Hennigan

#include <stdio.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>
#include "lib/list.h"
#include "lib/pq.h"
#include "lib/user_input.h"

#define STR_SZ 28

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

  return new_assign(cname, aname, pts, (date_t){ m, d });
}


int main() {
  pq_t * pq = pq_init(sizeof(assign_t), &compare);

  int i;
  for (i = 0; i < 5; i++) {
    assign_t * a = new_assign_prompt();
    pq_enqueue(pq, a);
    printf("\nCourse                      Assignment                  Points\tDue\n");
    printf("---------------------------------------------------------------------\n");
    list_iter(pq->list, &print_assignment);
    printf("\n\n");
  }

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
  } else if (t1 == t2 && a1->points > a2->points) {
    return true;
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

  printf("%s %s %d\t%d/%d\n", cname, aname,
         a->points, a->due.month, a->due.day);
}

assign_t * new_assign(char * cname, char * aname, int points, date_t due) {
  assign_t * a = malloc(sizeof(assign_t));
  snprintf(a->course_name, STR_SZ, "%s", cname);
  snprintf(a->assign_name, STR_SZ, "%s", aname);
  a->points = points;
  a->due = due;
  return a;
}
