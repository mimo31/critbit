#include "critbit.h"
#include "critbit-debug.h"

#include <stdlib.h>
#include <stdio.h>
#include <time.h>


int main(void) {

  const int time_base = TIME_UTC;

  // modified to preallocate memory for nodes
  // -> more accurate measurements
  cbt_t *t = cbt_alloc();

  struct timespec tstart, tend;

  timespec_get(&tstart, time_base);

  for (k_t k = 0; k < 10000000; k++)
    cbt_insert(t, k, 13);

  timespec_get(&tend, time_base);

  // #milliseconds taken
  const double ms = (tend.tv_sec - tstart.tv_sec) * 1e3
    + tend.tv_nsec * 1e-6
    - tstart.tv_nsec * 1e-6;

  printf("%.1f\n", ms);

  return EXIT_SUCCESS;
}
