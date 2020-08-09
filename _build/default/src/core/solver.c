#include "solver.h"
#include <stdio.h>

vars_t vars_set(vars_t vs, pos_t i, bool v) { return vs | ((v ? 1 : 0) << i); }

bool vars_get(vars_t vs, pos_t i) { return (vs & (1 << i)) != 0; }

/* == TEST == */

int main(int argc, char const *argv[]) {
  vars_t vs = 0;
  printf("value[2] = %d\n", vars_get(vs, 2));
  vs = vars_set(vs, 2, true);
  printf("value[2] = %d\n", vars_get(vs, 2));
}
