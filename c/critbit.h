#ifndef CRITBIT_H
#define CRITBIT_H

#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>

typedef int v_t;
typedef uint64_t k_t;

struct cbt;

typedef struct cbt cbt_t;

cbt_t *cbt_alloc(void);
void cbt_free(cbt_t *);

// returns 1 iff found and 0 otherwise; iff found, writes value into val_out
bool cbt_lookup(const cbt_t *, k_t, v_t *val_out);
void cbt_insert(cbt_t *, k_t, v_t);

// prints CBT into a file in a user-readable way (debug purposes)
// prints keys in hex! (but values in decimal)
void cbt_fprint(const cbt_t *, FILE *);

#endif // CRITBIT_H
