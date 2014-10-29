// src/list.c - Copyright 2014, Richard Hennigan

#include <stdlib.h>
#include <stdio.h>
#include "../lib/list.h"

node_t * node_init(void * data) {
  node_t * new_node = malloc(sizeof(node_t));
  new_node->data = data;
  new_node->prev = new_node;
  new_node->next = new_node;
  return new_node;
}

list_t * list_init(void) {
  node_t * new_node = node_init(NULL);
  list_t * new_list = malloc(sizeof(list_t));
  new_list->head = new_node;
  new_list->tail = new_node;
  new_list->length = 0;
  return new_list;
}

void list_insf(list_t * list, void * data) {
  if (list->length == 0) {
    free(list->head);
    list->head = node_init(data);
  } else {
    node_t * new_node = node_init(data);
    new_node->next = list->head;
    new_node->prev = list->tail;
    list->head->prev = new_node;
    list->tail->next = new_node;
    list->head = new_node;
  }
  list->length += 1;
}

void list_insr(list_t * list, void * data) {
  if (list->length == 0) {
    free(list->head);
    list->head = node_init(data);
  } else {
    node_t * new_node = node_init(data);
    new_node->next = list->head;
    new_node->prev = list->tail;
    list->head->prev = new_node;
    list->tail->next = new_node;
    list->tail = new_node;
  }
  list->length += 1;
}

void list_delf(list_t * list) {
  if (list->length == 0) {
    perror("list_delf: EMPTY");
    exit(EXIT_FAILURE);
  } else if (list->length == 1) {
    list_dispose(list);
    list = NULL;
    list = list_init();
  } else {
    node_t * first = list->head;
    list->head = first->next;
    list->head->prev = list->tail;
    list->tail->next = list->head;
    free(first);
    list->length -= 1;
  }
}

void list_delr(list_t * list) {
  if (list->length == 0) {
    perror("list_delr: EMPTY");
    exit(EXIT_FAILURE);
  } else if (list->length == 1) {
    list_dispose(list);
    list = NULL;
    list = list_init();
  } else {
    node_t * last = list->tail;
    list->tail = last->prev;
    list->tail->next = list->head;
    list->head->prev = list->tail;
    free(last);
    list->length -= 1;
  }
}

void list_dispose(list_t * list) {
  while (list-> head != list->tail) {
    list_delf(list);
  }
  free(list->head);
  free(list);
}
