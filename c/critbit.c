#include "critbit.h"

#include <stdlib.h>
#include <string.h>

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

// TODO replace recursion with while loops

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
    //return lookup_recursive(t->root, k, val_out);
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


// recursion OK here because only debug functionality

static
void print_one_indent(FILE *const f) {
  fprintf(f, "  ");
}

static
void print_indent(const unsigned amount, FILE *const f) {
  for (unsigned i = 0; i < amount; i++)
    print_one_indent(f);
}

static
void print_node_recursive(const node_t *n, const unsigned indent, FILE *const f) {
  if (n->internal) {
    print_indent(indent, f);
    fprintf(f, "%u {\n", n->cb);
    print_node_recursive(n->left, indent + 1, f);
    print_node_recursive(n->right, indent + 1, f);
    print_indent(indent, f);
    fprintf(f, "}\n");
  } else {
    print_indent(indent, f);
    fprintf(f, "(%lx, %d)\n", n->k, n->v);
  }
}

void cbt_fprint(const cbt_t *const t, FILE *const f) {
  if (t->root)
    print_node_recursive(t->root, 0, f);
  else
    fprintf(f, "(empty crit-bit tree)\n");
}
