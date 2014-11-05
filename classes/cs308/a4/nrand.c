#include <stdlib.h>
#include <stdio.h>
#include <sys/time.h>

int main() {
  unsigned short xsub[3];
  struct timeval randtime;
  gettimeofday(&randtime, (struct timezone *)0);
  xsub[0] = (ushort)(randtime.tv_usec);
  xsub[1] = (ushort)(randtime.tv_usec >> 16);
  xsub[2] = (ushort)(0);
  int i;
  for (i = 0; i < 100; i++) {
    printf("%ld\n", nrand48(xsub) & 7);
  }
  return 0;
}
