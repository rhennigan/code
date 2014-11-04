#include <stdio.h>
#include <time.h>

int main(int argc, char *argv[]) {
  clock_t start = clock();
  double sum = 0.0;
  int i;
  for (i = 1; i < 10000000; i++) {
    sum += 1.0 / (double)i;
  }
  printf("sum = %.4f (computed in %.4f seconds)\n",
         sum, (double)(clock() - start) / CLOCKS_PER_SEC);

  return 0;
}

