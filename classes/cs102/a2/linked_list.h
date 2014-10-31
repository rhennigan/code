#ifndef _LINKED_LIST_H
#define _LINKED_LIST_H

#define RAND_LIMIT 1024

#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>
#include <time.h>

#define HLINE printf("\n\n********************************************************************************\n");



typedef enum { false, true } bool;

typedef enum { Nil, Cons } list_e;

typedef struct int_list_s {
    list_e tag;
    int head;
    struct int_list_s *tail;
    } *int_list_t;



int_list_t int_list_init() {
    int_list_t list = malloc(sizeof(int_list_t));
    if (!list) {
        printf("Error: no space available\n");
        return NULL;
        }
    list->tag = Nil;
    list->head = 0;
    list->tail = NULL;
    return list;
    }



bool int_list_is_empty(int_list_t list) {
    return (!list || !list->tag);
    }



void int_list_dispose(int_list_t list) {
    while (!int_list_is_empty(list)) {
        int_list_t prev = list;
        list = list->tail;
        free(prev);
        }
    }



void _int_list_display(int_list_t list, uint64_t position) {
    if (position > 50) {
        printf("  ...\n");
        return;
        }
    else if (!int_list_is_empty(list)) {
        printf("  %lu: %d\n", position, list->head);
        _int_list_display(list->tail, position + 1);
        }
    else {
        return;
        }
    }



void int_list_display(int_list_t list) {
    int len = int_list_length(list);
    size_t cons_mem = sizeof(int_list_t) + sizeof(list_e);
    size_t int_mem = sizeof(int);
    size_t mem = (size_t) len * (cons_mem + int_mem) + sizeof(NULL);
    printf("\nList information:\n");
    printf("  element type:  %s\n", "int");
    printf("  element size:  %zu bytes\n", int_mem);
    printf("  cell size:     %zu bytes\n", cons_mem + int_mem);
    printf("  cell overhead: %zu bytes\n", cons_mem);
    printf("  mem_alloc:     %zu bytes\n", mem);
    printf("  mem_used:      %zu bytes\n", mem);
    printf("  max items:     unbounded\n");
    printf("  current items: %zu\n", len);
    printf("\nList data:\n");

    _int_list_display(list, 0);
    printf("\n");
    }



int_list_t int_list_cons(int head, int_list_t tail) {
    int_list_t list = malloc(sizeof(int_list_t));
    if (!list) {
        printf("Error: no space available\n");
        return NULL;
        }
    list->tag = Cons;
    list->head = head;
    list->tail = tail;
    return list;
    }



int int_list_length(int_list_t list) {
    return int_list_is_empty(list) ? 0 : 1 + int_list_length(list->tail);
    }



int int_list_get(int_list_t list, int position) {
    if (int_list_is_empty(list)) {
        printf("index out of range\n");
        exit(1);
        }
    else if (position == 0) {
        return list->head;
        }
    else {
        return int_list_get(list->tail, position - 1);
        }
    }



int_list_t int_list_append(int_list_t xs, int_list_t ys) {
    if (int_list_is_empty(xs)) {
        return ys;
        }
    else {
        free(xs);
        return int_list_cons(xs->head, int_list_append(xs->tail, ys));
        }
    }



int_list_t int_list_insert(int_list_t list, int position, int data) {
    if (int_list_is_empty(list) || position == 0) {
        return int_list_cons(data, list);
        }
    else {
        return int_list_cons(list->head, int_list_insert(list->tail,
                             position - 1,
                             data));
        }
    }



int_list_t int_list_remove(int_list_t list, int position) {
    if (position < 0) {
        printf("index out of range\n");
        exit(1);
        }
    else if (int_list_is_empty(list)) {
        return list;
        }
    else if (position == 0) {
        return list->tail;
        }
    else {
        return int_list_cons(list->head,
                             int_list_remove(list->tail, position - 1)
                            );
        }
    }



int_list_t int_list_random(size_t length) {
    srand((unsigned) time(NULL));

    int_list_t list = int_list_init();
    size_t i;
    for (i = 0; i < length; i++) {
        list = int_list_cons(rand() % RAND_LIMIT, list);
        }
    return list;
    }



int_list_t int_list_filter(int_list_t list, int max_val) {
    if (int_list_is_empty(list)) {
        return list;
        }
    else if (list->head > max_val) {
        return int_list_filter(list->tail, max_val);
        }
    else {
        return int_list_cons(list->head,
                             int_list_filter(list->tail, max_val));
        }
    }


#endif
