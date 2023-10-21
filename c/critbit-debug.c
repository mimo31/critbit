#include "critbit-debug.h"

#include "critbit-struct.h"

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

static
bool check_invariant_recursive(const node_t *const n, k_t *const p_bits, unsigned *const p_len) {
  if (n->internal) {
    if (n->cb >= sizeof(k_t) * 8)
      return false;

    k_t p_bits_l;
    unsigned p_len_l;
    if (!check_invariant_recursive(n->left, &p_bits_l, &p_len_l))
      return false;
    if (n->cb >= p_len_l)
      return false;
    if (p_bits_l & (k_t)1 << n->cb)
      return false;

    k_t p_bits_r;
    unsigned p_len_r;
    if (!check_invariant_recursive(n->right, &p_bits_r, &p_len_r))
      return false;
    if (n->cb >= p_len_r)
      return false;
    if (!(p_bits_r & (k_t)1 << n->cb))
      return false;

    const k_t before_cb = ~((k_t)-1 << n->cb);
    if ((before_cb & p_bits_l) != (before_cb & p_bits_r))
      return false;

    *p_bits = before_cb & p_bits_l;
    *p_len = n->cb;
  } else {
    *p_bits = n->k;
    *p_len = 8 * sizeof(k_t);
  }
  return true;
}

bool cbt_check_invariant(const cbt_t * const t) {
  if (!t->root)
    return true;
  k_t p_bits;
  unsigned p_len;
  return check_invariant_recursive(t->root, &p_bits, &p_len);
}
