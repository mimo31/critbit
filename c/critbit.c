#include "critbit-struct.h"

#include <stdlib.h>
#include <string.h>

node_t *node_pool;

cbt_t *cbt_alloc(void) {
  // allocate node pool
  // (assuming this will be called only once per program run, i.e.,
  // only one CBT per program run).
  // Also, we have to assume that the number of unique keys inserted
  // will be no more than half the number of node allocated here
  const size_t pool_bcount = (1 << 25) * sizeof(node_t);
  node_pool = malloc(pool_bcount);

  // write to memory to force allocation
  // (now instead of when first written later)
  for (size_t i = 0; i < pool_bcount; i++)
    ((char*)node_pool)[i] = 17;

  return calloc(1, sizeof(cbt_t));
}

static
void free_node_recursive(node_t *n) {
  // to make this non-recursive, we would need to build
  // our own stack or to add pointers to node parents into the tree
  if (!n)
    return;
  if (n->internal) {
    free_node_recursive(n->left);
    free_node_recursive(n->right);
  }
  free(n);
}

void cbt_free(cbt_t *t) {
  free_node_recursive(t->root);
  free(t);
}

static
const node_t *find_best_node(const node_t *n, const k_t k) {
  while (n->internal)
    n = k >> n->cb & 1 ? n->right : n->left;
  return n;
}

bool cbt_lookup(const cbt_t *const t, const k_t k, v_t *const val_out) {
  if (!t->root)
    return false;
  const node_t *n = find_best_node(t->root, k);
  const bool found = k == n->k;
  if (found)
    *val_out = n->v;
  return found;
}

// returns -1 iff keys are identical; otherwise, index of the critical bit
static
unsigned cb_index(const k_t k1, const k_t k2) {
  k_t diff = k1 ^ k2;
  if (!diff)
    return -1u;
  unsigned c = 0;
  while (!(diff & 1)) {
    diff >>= 1;
    c++;
  }
  return c;
}

static
node_t *alloc_node(void) {
  return node_pool++;
}

static
node_t *alloc_leaf(const k_t k, const v_t v) {
  node_t *n = alloc_node();
  n->internal = false;
  n->k = k;
  n->v = v;
  return n;
}

static
void insert_at(node_t *n, const k_t k, const v_t v, const unsigned cb) {
  while (n->internal && cb > n->cb)
    n = k >> n->cb & 1 ? n->right : n->left;
  node_t *new_leaf = alloc_leaf(k, v), *rest = alloc_node();
  memcpy(rest, n, sizeof(node_t));
  n->internal = true;
  n->cb = cb;
  if (k >> cb & 1) {
    n->left = rest;
    n->right = new_leaf;
  } else {
    n->left = new_leaf;
    n->right = rest;
  }
}

void cbt_insert(cbt_t *const t, const k_t k, const v_t v) {
  if (!t->root) {
    t->root = alloc_leaf(k, v);
    return;
  }

  // casting away const here ok because we
  // start from a non-const cbt
  node_t *n = (node_t *)find_best_node(t->root, k);
  const unsigned cb = cb_index(k, n->k);
  if (cb == -1u) {
    n->v = v;
    return;
  }

  // change t->root to n here
  insert_at(t->root, k, v, cb);
}
