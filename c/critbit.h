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

#endif // CRITBIT_H
