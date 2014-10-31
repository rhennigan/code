/*****************************************************************************/
/* Richard Hennigan                                                          */
/* cs308_hw1: main.c                                                         */
/* 2014-09-18                                                                */
/* Richard_Hennigan@student.uml.edu                                          */
/*****************************************************************************/

#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <signal.h>
#include <string.h>
#include <sys/wait.h>
#include <sys/resource.h>



typedef union {
  int exit_status;
  struct {
    unsigned sig_num:7;
    unsigned core_dmp:1;
    unsigned exit_num:8;
  } parts;
} LE_Wait_Status;



typedef struct {
  char owner[16];
  pid_t pid, ppid;
  int ruid, rgid;
  int euid, egid;
  int priority;
} pinfo;



LE_Wait_Status w_status_report(pinfo info) {
  LE_Wait_Status status;
  pid_t pID = info.pid;
  char *owner = info.owner;
  
  pid_t wstat = waitpid(pID, &status.exit_status, WUNTRACED);
  
  if (wstat == -1) {
    perror(strcat(owner, ": waitpid failure"));
    exit(EXIT_FAILURE);
  }

  if (WIFEXITED(status.exit_status)) {
    status.parts.exit_num = WEXITSTATUS(status.exit_status);
    printf("\n%s (pid = %d) exited with status: %d\n",
           owner, pID, status.parts.exit_num);
  }
  
  else if (WIFSTOPPED(status.exit_status)) {
    status.parts.sig_num = WSTOPSIG(status.exit_status);
    printf("\n%s (pid = %d) was stopped by a signal (%d)\n",
           owner, pID, status.parts.sig_num);
  }
  
  else if (WIFSIGNALED(status.exit_status)) {
    status.parts.sig_num = WTERMSIG(status.exit_status);
    status.parts.core_dmp = WCOREDUMP(status.exit_status);

    if (status.parts.core_dmp) {
      printf("\n%s (pid = %d) was terminated (core dumped) by a signal (%d)\n",
             owner, pID, status.parts.sig_num);
    }

    else {
      printf("\n%s (pid = %d) was terminated (no core dump) by a signal (%d)\n",
             owner, pID, status.parts.sig_num);
    }
    
  }

  fflush(stdout);
  return status;
}



void sig_handler(int signal){
  printf("\nCHILD: signal %d received; now calling execl(prof_prog)...", signal);
  if (execl("prof_prog", "prof_prog", NULL) == -1) {
    perror("\nCHILD: execl failure");
    exit(EXIT_FAILURE);
  }
}



pinfo process_report(char *owner) {
  pinfo info;

  int i;
  for (i = 0; i < 16; i++) {
    info.owner[i] = owner[i];
  }

  info.pid = getpid();
  info.ppid = getppid();
  info.ruid = getuid();
  info.euid = geteuid();
  info.rgid = getgid();
  info.egid = getegid();
  info.priority = getpriority(PRIO_PROCESS, 0);

  if (info.priority == -1) {
    perror(strcat(info.owner, ": getpriority failure"));
    exit(EXIT_FAILURE);
  }

  fflush(stdout);
  
  printf("\n\nProcess report:\n");
  printf("%s: Process ID is:        %d\n", info.owner, info.pid);
  printf("%s: Process parent ID is: %d\n", info.owner, info.ppid);
  printf("%s: Real UID is:          %d\n", info.owner, info.ruid);
  printf("%s: Real GID is:          %d\n", info.owner, info.rgid);
  printf("%s: Effective UID is:     %d\n", info.owner, info.euid);
  printf("%s: Effective GID is:     %d\n", info.owner, info.egid);
  printf("%s: Process priority is:  %d\n", info.owner, info.priority);
  printf("\n");

  fflush(stdout);

  return info;
}



void hline(int a, int b) {
  int i;
  for (i = 0; i < a; i++) {
    printf("%c", '\n');
  }
  for (i = 0; i < 80; i++) {
    printf("%c", '*');
  }
  for (i = 0; i < b; i++) {
    printf("%c", '\n');
  }
}



int main() {
  sigset_t mask, proc_mask;
  struct sigaction new;
  pid_t pID;
  int pipeline[2];
  pinfo info;

  hline(2, 1);

  // print out credentials
  process_report("PARENT");
  
  // create pipe with pipe call
  printf("\nPARENT: creating pipe...");
  if ((pipe(pipeline)) == -1) {
    perror("\nPARENT: pipe failure");
    exit(EXIT_FAILURE);
  };
  
  // fork child, blocking on pipe with read call
  printf("\nPARENT: forking process...");
  fflush(stdout);
  switch (pID = fork()) {

    case -1:
      perror("\nPARENT: fork failure");
      exit(EXIT_FAILURE);
      
    case 0: // PID belongs to CHILD
      printf("\nCHILD: now alive and installing sigfunc...");
      // child installs sigfunc with sigaction call
      sigemptyset(&proc_mask);
      sigprocmask(SIG_SETMASK, &proc_mask, NULL);
      
      sigemptyset(&mask);
      new.sa_mask = mask;
      new.sa_handler = sig_handler;
      new.sa_flags = 0;
      
      if(sigaction(SIGTERM, &new, NULL) == -1) {
	perror("\nCHILD: sigaction failure");
	exit(EXIT_FAILURE);
      }

      // child must print out credentials
      info = process_report("CHILD");

      // child must write pipe with write call
      printf("\nCHILD: closing read channel and writing info to pipe...");
      fflush(stdout);
      close(pipeline[0]);
      if ((write(pipeline[1], &info, sizeof(info))) == -1) {
        perror("\nCHILD: write failure");
        exit(EXIT_FAILURE);
      }
      printf("\nCHILD: wrote info to pipe");
      
      // child enters endless loop
      printf("\nCHILD: entering infinite loop");
      while (1) {}
      
    default:
      // parent wakes from pipe read (after child writes)
      printf("\nPARENT: closing write pipe and waiting for message from CHILD...");
      fflush(stdout);
      close(pipeline[1]);
      
      if (read(pipeline[0], &info, sizeof(info)) == -1) {
        perror("\nPARENT: read failure");
        exit(EXIT_FAILURE);
      }
      
      printf("\nPARENT: received info from: %s (pid = %d)", info.owner, info.pid);
      fflush(stdout);
      
      // parent sends SIGTERM to child pid with kill call
      printf("\nPARENT: sending kill signal (SIGTERM) to CHILD...");
      if (kill(pID, SIGTERM) == -1) {
        perror("\nPARENT: kill failure");
        exit(EXIT_FAILURE);
      }

      // parent blocks on wait call
      printf("\nPARENT: kill signal sent; now waiting for status...");
      w_status_report(info);
  }

  hline(1, 2);
  
  exit(EXIT_SUCCESS);
}
