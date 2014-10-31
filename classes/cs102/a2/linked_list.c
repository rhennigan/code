#include "linked_list.h"
#include <stdio.h>

int main()
{
    int items = 5;
    int add = 20;
    int take = 10;

    srand((unsigned) time(NULL));

    int_list_t list = int_list_init();
    printf("Running tests for int lists\n\n");
    printf("Filling list with %d random elements...\n", items);
    size_t i;
    for (i = 0; i < items; i++) {
        list = int_list_cons(rand(), list);
    }
    int_list_display(list);

    printf("Filling list at %d random locations...\n", add);
    uint64_t count = int_list_length(list);
    size_t j;
    for (j = 0; j < add; j++) {
        list = int_list_insert(list, rand() % ++count, (int) j);
    }
    int_list_display(list);

    printf("Removing %d elements at random locations...\n", take);
    count = int_list_length(list);
    size_t k;
    for (k = 0; k < take; k++) {
        list = int_list_remove(list, rand() % --count);
    }
    int_list_display(list);

    int_list_dispose(list);
    HLINE;

    return 0;
}
