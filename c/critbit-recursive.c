#include "critbit-struct.h"

#include <stdlib.h>
#include <string.h>

cbt_t *cbt_alloc(void) {
  return calloc(1, sizeof(cbt_t));
}

static
void free_node_recursive(node_t *n) {
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
const node_t *find_best_node(const node_t *const n, const k_t k) {
  if (n->internal) {
    return find_best_node(k >> n->cb & 1 ? n->right : n->left, k);
  } else {
    return n;
  }
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
  return malloc(sizeof(node_t));
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
void insert_at(node_t *const n, const k_t k, const v_t v, const unsigned cb) {
  if (!n->internal || cb < n->cb) {
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
  } else {
    insert_at(k >> n->cb & 1 ? n->right : n->left, k, v, cb);
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

  insert_at(n, k, v, cb);
}
