#ifndef _ARRAY_H
#define _ARRAY_H

#define RAND_LIMIT 1024

#include <stdlib.h>
#include <stdio.h>
#include <stddef.h>

#define HLINE printf("\n\n********************************************************************************\n");


typedef struct int_array_s {
    size_t mem_alloc;
    size_t mem_used;
    size_t length;
    int *data;
} int_array_t;



int_array_t *int_array_init(size_t length)
{
    int_array_t *array = malloc(sizeof(int_array_t));
    if (!array)
        return NULL;

    array->data = malloc(sizeof(int) * length);
    if (!array->data) {
        free(array);
        return NULL;
    }

    array->mem_alloc = sizeof(int) * length;
    array->mem_used = 0;
    array->length = length;

    return array;
}



int int_array_length(int_array_t * array)
{
    return array->mem_used / sizeof(int);
}


void int_array_dispose(int_array_t * array)
{
    free(array->data);
    free(array);
}



int int_array_get(int_array_t * array, int position)
{
    return array->data[position];
}



void int_array_display(int_array_t * array, int max_items)
{
    printf("\nArray information:\n");
    printf("  element type:  %s\n", "int");
    printf("  element size:  %zu bytes\n", sizeof(int));
    printf("  mem_alloc:     %zu bytes\n", array->mem_alloc);
    printf("  mem_used:      %zu bytes\n", array->mem_used);
    printf("  max items:     %zu\n", array->length);
    printf("  current items: %zu\n", array->mem_used / sizeof(int));
    printf("\nArray data:\n");

    uint64_t i, limit = array->mem_used / sizeof(int);
    for (i = 0; i < limit; i++) {
        if (i >= max_items) {
            printf("  [...]\n");
            break;
        } else {
            printf("  %lu: %d\n", i, array->data[i]);
        }
    }
    printf("\n");
}



void int_array_insert(int_array_t * array, uint64_t position, int object)
{
    if (position < 0 || position > array->length - 1) {
        printf("index out of range\n");
        exit(1);
    }
    if (array->mem_used + sizeof(int) > array->mem_alloc) {
        printf("array out of memory\n");
        exit(1);
    }

    else {
        uint64_t items = array->mem_used / sizeof(int);
        uint64_t i = items;
        for (i = items; i > position; i--) {
            array->data[i] = array->data[i - 1];
        }

        array->data[position] = object;
        array->mem_used += sizeof(int);
    }
}



void int_array_remove(int_array_t * array, uint64_t position)
{
    if (position < 0 || position > array->length - 1) {
        printf("index out of range\n");
        exit(1);
    } else {
        uint64_t i;
        uint64_t items = array->mem_used / sizeof(int);
        for (i = position; i < items - 1; i++) {
            array->data[i] = array->data[i + 1];
        }
        array->mem_used -= sizeof(int);
    }
}



double drand()
{
    return (double) rand() / (double) rand() + (double) rand();
}



int_array_t *int_array_random(size_t max_length, size_t items)
{
    int_array_t *array = int_array_init(max_length);
    size_t i;
    for (i = 0; i < items; i++) {
        int_array_insert(array, i, ((int) rand()) % RAND_LIMIT);
    }
    return array;
}

void int_array_filter(int_array_t * array, int max_val)
{
    uint64_t i, limit = array->mem_used / sizeof(int);
    for (i = 0; i < limit; i++) {
        if (array->data[i] > max_val) {
            int_array_remove(array, i);
        };
    }
}

#endif
