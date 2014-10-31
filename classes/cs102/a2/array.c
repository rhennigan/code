#include "array.h"
#include <stdio.h>

int main()
{
    size_t items = 5;
    size_t add = 20;
    size_t take = 10;
    size_t max_length = 50;

    srand((unsigned) time(NULL));

    int_array_t *array = int_array_init(max_length);
    printf("Running tests for <%s> arrays\n\n", "int");
    printf("Filling array with %d random elements...\n", items);
    size_t i;
    for (i = 0; i < items; i++) {
        int_array_insert(array, i, (int) drand());
    }
    int_array_display(array, 25);

    printf("Filling array at %d random locations...\n", add);
    uint64_t count = int_array_length(array);
    printf("count = %d\n", count);
    size_t j;
    for (j = 0; j < add; j++) {
        int_array_insert(array, rand() % count++, (int) j);
    }
    int_array_display(array, 25);

    printf("Removing %d elements at random locations...\n", take);
    count = int_array_length(array);
    size_t k;
    for (k = 0; k < take; k++) {
        int_array_remove(array, rand() % --count);
    }
    int_array_display(array, 25);

    int_array_dispose(array);
    HLINE;

    return 0;
}
