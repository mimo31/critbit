#include "critbit.h"
#include "critbit-print.h"

#include <stdlib.h>
#include <stdio.h>

// a test is supposed to consist of a sequence of these
// one step is one operation on the CBT:
//   - an insert modifies the tree
//   - a look-up queries the tree and we should check if the result is as expected
typedef struct teststep {
  bool is_insert;    // whether this step is an insert (in contrast to a look-up)
  k_t k;             // key to use for the operation
  bool present;      // if insert: don't care
                     // if look-up: whether to expect some value
  v_t v;             // if insert: value to insert
                     // if look-up: value to expect (don't care if present is false)
} ts_t;

void runtest(const char *const name, const ts_t *const steps, const unsigned step_count) {
  printf("RUNNING TEST %s\n", name);
  cbt_t *t = cbt_alloc();
  for (unsigned i = 0; i < step_count; i++) {
    const ts_t step = steps[i];
    if (step.is_insert) {
      cbt_insert(t, step.k, step.v);
    } else {
      v_t got;
      const bool status = cbt_lookup(t, step.k, &got);
      if (status && !step.present)
        printf("got a value but shouldn't have\n");
      else if (!status && step.present)
        printf("didn't get a value but should have\n");
      else if (status && got != step.v)
        printf("got a wrong value\n");
      else
        continue;
      exit(-1);
    }
  }
  cbt_fprint(t, stdout);
  cbt_free(t);
  printf("TEST %s PASSED\n", name);
}

ts_t insert_step(const k_t k, const v_t v) {
  return (ts_t){ true, k, false, v };
}

ts_t present_lookup_step(const k_t k, const v_t v) {
  return (ts_t){ false, k, true, v };
}

ts_t missing_lookup_step(const k_t k) {
  return (ts_t){ false, k, false, -1 };
}

int main(void) {
  const ts_t T1[] = {
    missing_lookup_step(13),
    insert_step(3, 9),
    missing_lookup_step(13),
    present_lookup_step(3, 9),
    insert_step(3, 27),
    present_lookup_step(3, 27),
    missing_lookup_step(2),
  };
  const ts_t T2[] = {
    insert_step(0, 0),
    insert_step(1, 1),
    insert_step(2, 4),
    insert_step(3, 9),
    insert_step(4, 16),
    present_lookup_step(0, 0),
    present_lookup_step(1, 1),
    present_lookup_step(2, 4),
    present_lookup_step(3, 9),
    present_lookup_step(4, 16),
  };
  const ts_t T3[] = {
    insert_step(128, 17),
    insert_step(256, 34),
    missing_lookup_step(64),
    missing_lookup_step(192),
    missing_lookup_step(512),
    present_lookup_step(256, 34),
    present_lookup_step(128, 17),
    insert_step(192, 78),
    insert_step(128, 15),
    missing_lookup_step(64),
    missing_lookup_step(512),
    present_lookup_step(256, 34),
    present_lookup_step(192, 78),
    present_lookup_step(128, 15),
  };
  runtest("1", T1, sizeof(T1) / sizeof(ts_t));
  runtest("2", T2, sizeof(T2) / sizeof(ts_t));
  runtest("3", T3, sizeof(T3) / sizeof(ts_t));

  printf("ALL TESTS PASSED\n");

  return EXIT_SUCCESS;
}
