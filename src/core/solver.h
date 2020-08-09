#ifndef SOLVER_H
#define SOLVER_H

#include <stdbool.h>
#include <stdint.h>

/**
 * @brief Type to model a set of 64 variables
 *
 */
typedef int64_t vars_t;

/**
 * @brief Type alias for variable position
 *
 */
typedef uint8_t pos_t;

/**
 * @brief Assign a value v to the ith variable of a variable set
 *
 * @param vs  The variable set
 * @param i   The position (integer between 0 and 63 included)
 * @param v   The value to assign
 * @return vars_t
 */
vars_t vars_set(vars_t vs, pos_t i, bool v);

/**
 * @brief Get the boolean value of the ith variable in
 * a variable set
 *
 * @param vs  The variable set
 * @param i   The position (integer between 0 and 63 included)
 */
bool vars_get(vars_t vs, pos_t i);

#endif