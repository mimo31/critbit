#ifndef CRITBIT_PRINT_H
#define CRITBIT_PRINT_H

#include <stdio.h>

#include "critbit.h"

// prints CBT into a file in a user-readable way (debug purposes)
// prints keys in hex! (but values in decimal)
void cbt_fprint(const cbt_t *, FILE *);

#endif // CRITBIT_PRINT_H
