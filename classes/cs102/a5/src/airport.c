#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>
#include <time.h>
#include "../lib/queue.h"
#include "../lib/user_input.h"

#define C_RED     "\x1b[31m"
#define C_GREEN   "\x1b[32m"
#define C_YELLOW  "\x1b[33m"
#define C_BLUE    "\x1b[34m"
#define C_MAGENTA "\x1b[35m"
#define C_CYAN    "\x1b[36m"
#define C_RESET   "\x1b[0m"

typedef struct plane_s {
  int num;
  bool arriving;
} plane_t;

typedef struct runway_s {
  bool vacant;
  int time_to_vac;
  plane_t current_plane;
} runway_t;

void hline();
void new_plane(bool arr, char * lbl, size_t s, const char * str);

queue_t * air_queue;
queue_t * gnd_queue;

/*
  If command line arguments are supplied, the program will run in quiet mode
  by suppressing all output and getting user input as commandline options
  instead of interactively.
  
  arguments:
  auto
  arrival_air_prob
  arrival_gnd_prob
  time_duration
  seed_offset
*/
int main(int argc, char *argv[]) {
  air_queue = queue_init();
  gnd_queue = queue_init();
  runway_t runway = { true, 0, (plane_t){ -1, false } };
  double rand_air, rand_gnd;
  double arrival_air_prob, arrival_gnd_prob;
  int time_duration;
  int seed_offset;
  int departures = 0, arrivals = 0;

  /* We save a file descriptor for stdout, so that if we close it, we'll be
     able to reopen it later */
  int stdout_cpy = dup(STDOUT_FILENO);
  bool auto_mode = argc == 6 && strcmp(argv[1], "auto") == 0;

  /* If we're running in auto mode, we'll suppress output */
  if (auto_mode) {
    close(STDOUT_FILENO);
  }

  /* If we're running in auto mode, parameters are obtained from the
     command line arguments instead of interactively */
  if (auto_mode) {
    arrival_air_prob = atof(argv[2]);
    arrival_gnd_prob = atof(argv[3]);
    time_duration = atoi(argv[4]);
    seed_offset = atoi(argv[5]);
  } else {
    int i;
    for (i = 0; i < 24; i++) {
      printf("\n");
    }
    printf(" enter a value between 0 and 1 for air arrival probability: ");
    arrival_air_prob = get_input_double(0.0, 1.0);
    printf(" enter a value between 0 and 1 for ground arrival probability: ");
    arrival_gnd_prob = get_input_double(0.0, 1.0);
    printf(" enter a value between 1 and 20 for the time duration: ");
    time_duration = get_input_int(1, 20);
  }

  srand48((unsigned) time(NULL) + seed_offset);

  int sec;
  for (sec = 0; sec < time_duration; sec++) {
    hline();
    printf("\n SIMULATION IN PROGRESS");
    printf("\n\n time elapsed: %d\n\n", sec);
    printf(" queue status:\n  A|");
    int i;
    for (i = 0; i < queue_size(air_queue); i++) {
      printf("*");
    }
    printf("\n  G|");
    for (i = 0; i < queue_size(gnd_queue); i++) {
      printf("*");
    }
    printf("\n\n");
    printf(" runway status:\n   |");

    if (!runway.current_plane.arriving) {
      for (i = 0; i < 2 - runway.time_to_vac; i++) {
        printf("  ");
      }
      printf(runway.vacant ? " " : "*");
      for (i = 0; i < runway.time_to_vac; i++) {
        printf("  ");
      }
    } else {
      for (i = 0; i < runway.time_to_vac; i++) {
        printf("  ");
      }
      printf(runway.vacant ? " " : "*");
      for (i = 0; i < 2 - runway.time_to_vac; i++) {
        printf("  ");
      }
    }
    printf("| %s", runway.vacant ? C_GREEN "CLEAR" : C_RED "IN USE");
    if (!runway.vacant) {
      if (runway.current_plane.arriving) {
        printf(C_RESET " #%d landing\n\n", runway.current_plane.num);
      } else {
        printf(C_RESET " #%d departing\n\n", runway.current_plane.num);
      }
    } else {
      printf(C_RESET "\n\n");
    }

    /* Check for possible arrivals */
    rand_air = drand48();
    rand_gnd = drand48();

    char arriving_1[5], arriving_2[7], departing[5];
    if (rand_air < arrival_air_prob) {
      new_plane(true, arriving_1, sizeof(arriving_1), "#%d");
    } else {
      snprintf(arriving_1, sizeof(arriving_1), "    ");
    }

    if (rand_air < arrival_air_prob * arrival_air_prob) {
      new_plane(true, arriving_2, sizeof(arriving_2), ", #%d");
    } else {
      snprintf(arriving_2, sizeof(arriving_2), "      ");
    }

    if (rand_gnd < arrival_gnd_prob) {
      new_plane(false, departing, sizeof(departing), "#%d");
    } else {
      snprintf(departing, sizeof(departing), "    ");
    }

    printf(" new requests:\n");
    printf("  landing:   %s%s\n", arriving_1, arriving_2);
    printf("  departing: %s\n", departing);

    /* If the runway is open and planes are waiting to land, bring one in */
    printf("\n updates:\n");
    if (runway.vacant) {
      /* Give priority to planes waiting to land */
      if (!queue_isempty(air_queue)) {
        runway.vacant = false;   // a plane is landing
        runway.time_to_vac = 2;  // time needed to clear the runway
        queue_dequeue(air_queue, &runway.current_plane);
        printf("  plane #%d is on final approach\n", runway.current_plane.num);
      } else {
        /* No planes waiting to land, check for departures */
        if (!queue_isempty(gnd_queue)) {
          runway.vacant = false;   // a plane is departing
          runway.time_to_vac = 2;  // time needed to clear the runway
          queue_dequeue(gnd_queue, &runway.current_plane);
          printf("  plane #%d is now departing\n", runway.current_plane.num);
        } else {
          /* Nothing to do! */
          printf("  the airport is idle\n");
        }
      }
    } else {
      /* Runway is in use, so we'll keep it moving along */
      if (runway.time_to_vac == 0) {
        bool arr = runway.current_plane.arriving;
        if (arr) {
          arrivals++;
        } else {
          departures++;
        }
        printf("  plane #%d has successfully %s and cleared the runway\n",
               runway.current_plane.num, arr ? "landed" : "departed");
        runway.vacant = true;
        runway.current_plane = (plane_t){ -1, false };
      } else {
        runway.time_to_vac--;
        printf("\n");
      }
    }
    printf("\n");
    hline();

    /* There's no sense in sleeping if we're in auto mode,
       we just want the data */
    if (!auto_mode) {
      fflush(NULL);
      sleep(3);
      printf("\n");
    }
  }

  /* If we're in auto mode, we'll reopen stdout and only print the results */
  if (auto_mode) {
    fflush(NULL);
    dup2(stdout_cpy, STDOUT_FILENO);
    close(stdout_cpy);
    printf("%f, %f, %d, %d, %d, %d, %d\n",
           arrival_air_prob, arrival_gnd_prob, time_duration,
           queue_size(air_queue), queue_size(gnd_queue),
           arrivals, departures);
  }
  return 0;
}

void hline() {
  printf("\n");
  int i;
  for (i = 0; i < 80; i++) { printf("-"); }
  printf("\n");
}

void new_plane(bool arr, char * lbl, size_t s, const char * str) {
  plane_t * airplane = malloc(sizeof(plane_t));
  airplane->num = lrand48() % 900 + 100;
  airplane->arriving = arr;
  if (arr) {
    queue_enqueue(air_queue, airplane);
  } else {
    queue_enqueue(gnd_queue, airplane);
  }
  snprintf(lbl, s, str, airplane->num);
}
