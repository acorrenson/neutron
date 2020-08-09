#include "list.h"
#include <stdio.h>
#include <stdlib.h>

struct node_s {
  void *val;
  struct node_s *next;
};

struct list_s {
  unsigned int size;
  struct node_s *head;
};

list_t list_empty() {
  struct list_s *ls = malloc(sizeof(struct list_s));
  ls->size = 0;
  ls->head = NULL;
  return ls;
}

void list_append(list_t ls, void *v) {
  struct node_s *new_node = malloc(sizeof(struct node_s));
  new_node->val = v;
  new_node->next = ls->head;
  ls->head = new_node;
  ls->size = ls->size + 1;
}

void list_remove(list_t ls, unsigned int i) {
  if (ls->size == 0) {
    return;
  }
  unsigned int counter = 0;
  struct node_s *next = ls->head->next;
  struct node_s **insert = &(ls->head);
  while (i) {
    i--;
    insert = &((*insert)->next);
    next = next->next;
  }
  free(*insert);
  *insert = next;
  ls->size--;
}

int main(int argc, char const *argv[]) {
  list_t ls = list_empty();
  list_append(ls, (void *)1);
  list_append(ls, (void *)2);
  list_append(ls, (void *)3);
  list_append(ls, (void *)4);

  printf("size = %d\n", ls->size);
  struct node_s *ptr = ls->head;
  for (int i = 0; i < 4; i++) {
    printf("ls[%d] = %d\n", i, (int)ptr->val);
    ptr = ptr->next;
  }

  printf("--\n");
  list_remove(ls, 1);
  ptr = ls->head;
  for (int i = 0; i < ls->size; i++) {
    printf("ls[%d] = %d\n", i, (int)ptr->val);
    ptr = ptr->next;
  }

  printf("--\n");
  list_remove(ls, 0);
  ptr = ls->head;
  for (int i = 0; i < ls->size; i++) {
    printf("ls[%d] = %d\n", i, (int)ptr->val);
    ptr = ptr->next;
  }

  printf("--\n");
  list_remove(ls, 1);
  ptr = ls->head;
  for (int i = 0; i < ls->size; i++) {
    printf("ls[%d] = %d\n", i, (int)ptr->val);
    ptr = ptr->next;
  }

  return 0;
}
