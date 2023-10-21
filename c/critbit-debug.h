#ifndef CRITBIT_DEBUG_H
#define CRITBIT_DEBUG_H

#include <stdio.h>

#include "critbit.h"

// prints CBT into a file in a user-readable way (debug purposes)
// prints keys in hex! (but values in decimal)
void cbt_fprint(const cbt_t *, FILE *);

// checks a given CBT is really a consisten CBT (our invariant holds in it)
// returns true iff invariant holds
bool cbt_check_invariant(const cbt_t *);

#endif // CRITBIT_DEBUG_H
