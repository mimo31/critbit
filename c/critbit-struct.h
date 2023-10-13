#ifndef CRITBIT_STRUCT_H
#define CRITBIT_STRUCT_H

#include "critbit.h"

struct cbt_node;
typedef struct cbt_node node_t;

struct cbt_node {
  bool internal;
  union {
    struct {
      unsigned cb; // critical bit (index of)
      node_t *left, *right;
    };
    struct {
      k_t k;
      v_t v;
    };
  };
};

struct cbt {
  node_t *root;
};

#endif // CRITBIT_STRUCT_H
