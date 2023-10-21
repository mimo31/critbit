#include "critbit.h"
#include "critbit-debug.h"

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

void report_and_exit_if_wrong(const bool exp_pres, const v_t exp_val,
    const bool act_pres, const v_t act_val) {
  if (act_pres && !exp_pres)
    printf("got a value but shouldn't have\n");
  else if (!act_pres && exp_pres)
    printf("didn't get a value but should have\n");
  else if (act_pres && exp_val != act_val)
    printf("got a wrong value\n");
  else
    return;
  exit(-1);
}

void report_and_exit_if_inconsistent(const cbt_t *const t) {
  if (cbt_check_invariant(t))
    return;
  printf("invariant doesn't hold\n");
  exit(-1);
}

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
      report_and_exit_if_wrong(step.present, step.v, status, got);
    }
    report_and_exit_if_inconsistent(t);
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

typedef struct rand_test {
  unsigned seed;
  k_t keys_from, keys_to;
  size_t opcount;
  bool check_invariant;
} rand_test_t;

void run_rand_test(const rand_test_t params) {
  srand(params.seed);
  const int num_keys = params.keys_to - params.keys_from;
  bool *present = calloc(num_keys, sizeof(bool));
  v_t *values = malloc(sizeof(v_t) * num_keys);
  cbt_t *t = cbt_alloc();
  if (params.check_invariant)
    report_and_exit_if_inconsistent(t);
  for (size_t i = 0; i < params.opcount; i++) {
    const size_t ki = ((size_t)rand()) % num_keys;
    const k_t k = ki + params.keys_to;
    if (rand() & 1) {
      const v_t v = rand();
      present[ki] = true;
      values[ki] = v;
      cbt_insert(t, k, v);
    } else {
      v_t got;
      const bool status = cbt_lookup(t, k, &got);
      report_and_exit_if_wrong(present[ki], values[ki], status, got);
    }
    if (params.check_invariant)
      report_and_exit_if_inconsistent(t);
  }
  cbt_free(t);
  free(present);
  free(values);
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
  const ts_t T4[] = {
    insert_step(0, 7),
    insert_step(1, 7),
    insert_step(8, 7),
    insert_step(9, 7),
    insert_step(4, 47),
    insert_step(5, 57),
    insert_step(6, 67),
    present_lookup_step(6, 67),
    present_lookup_step(5, 57),
    present_lookup_step(4, 47),
    present_lookup_step(9, 7),
    present_lookup_step(8, 7),
    present_lookup_step(1, 7),
    present_lookup_step(0, 7)
  };
  runtest("1", T1, sizeof(T1) / sizeof(ts_t));
  runtest("2", T2, sizeof(T2) / sizeof(ts_t));
  runtest("3", T3, sizeof(T3) / sizeof(ts_t));
  runtest("4", T4, sizeof(T4) / sizeof(ts_t));

  const rand_test_t RT[] = {
    { 42, 1024, 2048, 10000, true },
    { 42, 0, 4096, 1000000, false }
  };

  for (size_t i = 0; i < sizeof(RT) / sizeof(RT[0]); i++) {
    printf("rand test: seed = %u, keys in [%lu, %lu), %lu operation(s)\n",
        RT[i].seed, RT[i].keys_from, RT[i].keys_to, RT[i].opcount);
    run_rand_test(RT[i]);
  }

  printf("ALL TESTS PASSED\n");

  return EXIT_SUCCESS;
}
