#include <omp.h>
#include <stdio.h>

int main() {
  /* omp_set_num_threads(4); */
  #pragma omp parallel
  {
    int ID = omp_get_thread_num();
    #pragma omp for
    for (int i = 0; i <= 10; i++) {
      printf(" hello(%d, %d) ", ID, i);
      printf(" world(%d, %d) \n", ID, i);
    }
  }
}
