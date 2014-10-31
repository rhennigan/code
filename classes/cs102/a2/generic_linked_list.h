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




#define def_generic_list(TYPE)                  \
                                                \
    typedef struct TYPE##_list_s {              \
        list_e tag;                             \
        TYPE head;                              \
        struct TYPE##_list_s *tail;             \
    } *TYPE##_list_t;                           \
                                                \
                                                \
                                                \
    TYPE##list_t TYPE##list_init()              \
    {                                                   \
        TYPE##list_t list = malloc(sizeof(TYPE##list_t));       \
        if (!list) {                                            \
            printf("Error: no space available\n");              \
            return NULL;                                        \
        }                                                       \
        list->tag = Nil;                                        \
        list->head = 0;                                         \
        list->tail = NULL;                                      \
        return list;                                            \
    }                                                           \
                                                                \
                                                                \
                                                                \
    bool TYPE##list_is_empty(TYPE##list_t list)                 \
    {                                                           \
        return (!list || !list->tag);                           \
    }                                                           \
                                                                \
                                                                \
                                                                \
    void TYPE##list_dispose(TYPE##list_t list)                  \
    {                                                           \
        while (!TYPE##list_is_empty(list)) {                    \
            TYPE##list_t prev = list;                           \
            list = list->tail;                                  \
            free(prev);                                         \
        }                                                       \
    }                                                           \
                                                                \
                                                                \
                                                                \
    void _TYPE##list_display(TYPE##list_t list, uint64_t position)      \
    {                                                                   \
        if (position > 50) {                                            \
            printf("  ...\n");                                          \
            return;                                                     \
        } else if (!TYPE##list_is_empty(list)) {                        \
            printf("  %lu: %d\n", position, list->head);                \
            _TYPE##list_display(list->tail, position + 1);              \
        } else {                                                        \
            return;                                                     \
        }                                                               \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    void TYPE##list_display(TYPE##list_t list)                          \
    {                                                                   \
        int len = TYPE##list_length(list);                              \
        size_t cons_mem = sizeof(TYPE##list_t) + sizeof(list_e);        \
        size_t TYPE##mem = sizeof(int);                                 \
        size_t mem = (size_t) len * (cons_mem + TYPE##mem) + sizeof(NULL); \
        printf("\nList information:\n");                                \
        printf("  element type:  %s\n", "int");                         \
        printf("  element size:  %zu bytes\n", TYPE##mem);              \
        printf("  cell size:     %zu bytes\n", cons_mem + TYPE##mem);   \
        printf("  cell overhead: %zu bytes\n", cons_mem);               \
        printf("  mem_alloc:     %zu bytes\n", mem);                    \
        printf("  mem_used:      %zu bytes\n", mem);                    \
        printf("  max items:     unbounded\n");                         \
        printf("  current items: %zu\n", len);                          \
        printf("\nList data:\n");                                       \
                                                                        \
        _TYPE##list_display(list, 0);                                   \
        printf("\n");                                                   \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    TYPE##list_t TYPE##list_cons(int head, TYPE##list_t tail)           \
    {                                                                   \
        TYPE##list_t list = malloc(sizeof(TYPE##list_t));               \
        if (!list) {                                                    \
            printf("Error: no space available\n");                      \
            return NULL;                                                \
        }                                                               \
        list->tag = Cons;                                               \
        list->head = head;                                              \
        list->tail = tail;                                              \
        return list;                                                    \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    int TYPE##list_length(TYPE##list_t list)                            \
    {                                                                   \
        return TYPE##list_is_empty(list) ? 0 : 1 + TYPE##list_length(list->tail); \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    int TYPE##list_get(TYPE##list_t list, int position)                 \
    {                                                                   \
        if (TYPE##list_is_empty(list)) {                                \
            printf("index out of range\n");                             \
            exit(1);                                                    \
        } else if (position == 0) {                                     \
            return list->head;                                          \
        } else {                                                        \
            return TYPE##list_get(list->tail, position - 1);            \
        }                                                               \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    TYPE##list_t TYPE##list_append(TYPE##list_t xs, TYPE##list_t ys)    \
    {                                                                   \
        if (TYPE##list_is_empty(xs)) {                                  \
            return ys;                                                  \
        } else {                                                        \
            free(xs);                                                   \
            return TYPE##list_cons(xs->head, TYPE##list_append(xs->tail, ys)); \
        }                                                               \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    TYPE##list_t TYPE##list_insert(TYPE##list_t list, int position, int data) \
    {                                                                   \
        if (TYPE##list_is_empty(list) || position == 0) {               \
            return TYPE##list_cons(data, list);                         \
        } else {                                                        \
            return TYPE##list_cons(list->head, TYPE##list_insert(list->tail, \
                                                                 position - 1, \
                                                                 data)); \
        }                                                               \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    TYPE##list_t TYPE##list_remove(TYPE##list_t list, int position)     \
    {                                                                   \
        if (position < 0) {                                             \
            printf("index out of range\n");                             \
            exit(1);                                                    \
        } else if (TYPE##list_is_empty(list)) {                         \
            return list;                                                \
        } else if (position == 0) {                                     \
            return list->tail;                                          \
        } else {                                                        \
            return TYPE##list_cons(list->head,                          \
                                   TYPE##list_remove(list->tail, position - 1) \
                                   );                                   \
        }                                                               \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    TYPE##list_t TYPE##list_random(size_t length)                       \
    {                                                                   \
        srand((unsigned) time(NULL));                                   \
                                                                        \
        TYPE##list_t list = TYPE##list_init();                          \
        size_t i;                                                       \
        for (i = 0; i < length; i++) {                                  \
            list = TYPE##list_cons(rand() % RAND_LIMIT, list);          \
        }                                                               \
        return list;                                                    \
    }                                                                   \
                                                                        \
                                                                        \
                                                                        \
    TYPE##list_t TYPE##list_filter(TYPE##list_t list, int max_val)      \
    {                                                                   \
        if (TYPE##list_is_empty(list)) {                                \
            return list;                                                \
        } else if (list->head > max_val) {                              \
            return TYPE##list_filter(list->tail, max_val);              \
        } else {                                                        \
            return TYPE##list_cons(list->head,                          \
                                   TYPE##list_filter(list->tail, max_val)); \
        }                                                               \
    }


#endif
