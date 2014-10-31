#include <stdlib.h>
#include "../lib/list.h"

node_t * node_init(void * data) {
  node_t * new_node = malloc(sizeof(node_t));
  new_node->data = data;
  new_node->prev = NULL;
  new_node->next = NULL;
  return new_node;
}

list_t * list_init(void) {
  node_t * new_node = node_init(NULL);
  list_t * new_list = malloc(sizeof(list_t));
  new_list->head = new_node;
  new_list->tail = new_node;
  new_list->head->next = new_list->tail;
  new_list->length = 1;
  return new_list;
}

void list_insert(list_t * list, void * data) {
  node_t * new_node = node_init(data);
  if (list->length == 0) {
    list->tail = new_node;
    list->head = new_node;
  } else {
    new_node->next = list->head;
    list->head->prev = new_node;
    list->head = new_node;
  }
  list->length += 1;
}

void list_append(list_t * list, void * data) {
  node_t * new_node = node_init(data);
  if (list->length == 0) {
    list->tail = new_node;
    list->head = new_node;
  } else {
    new_node->prev = list->tail;
    list->tail->next = new_node;
    list->tail = new_node;
  }
  list->length += 1;
}

void list_delete(list_t * list) {
  node_t * temp = list->head;
  list->head = list->head->next;
  if (temp != NULL) free(temp);
  list->length -= 1;
}

void list_dispose(list_t * list) {
  while (list-> head != list->tail) {
    list_delete(list);
  }
  free(list->head);
  free(list);
}
