#include "critbit-print.h"

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
