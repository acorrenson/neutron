#ifndef LIST_H
#define LIST_H

struct node_s;
typedef struct list_s *list_t;

/**
 * @brief Return an empty list
 *
 * @return list_t
 */
list_t list_empty();

/**
 * @brief Append a value to a list
 *
 * @param ls  The list
 * @param v   The value to add
 */
void list_append(list_t ls, void *v);

/**
 * @brief Remove the ith value of a list
 *
 * @param ls  The list
 * @param i   The index
 */
void list_remove(list_t ls, unsigned int i);

/**
 * @brief Get the ith element of a list
 *
 * @param ls      The list
 * @param i       The index
 * @return void*  The ith element
 */
void *list_get(list_t ls, unsigned int i);

/**
 * @brief Set the ith value of a list
 *
 * @param ls  The list
 * @param i   The index
 * @param v   The new value
 */
void list_set(list_t ls, unsigned int i, void *v);

#endif