#include "linked_list.h"
#include <stdio.h>


typedef struct record_s {
    int count;
    int ticks;
    double seconds;
} record_t;

void record_display(record_t record)
{
    printf("    Count: %d, CPU ticks: %d, Seconds: %f\n",
           record.count, record.ticks, record.seconds);
}



void write_data(char *file_name, int count, record_t * records)
{
    int i;
    FILE *file = fopen(file_name, "a");
    for (i = 0; i < count; i++) {
        fprintf(file, "%d, %d, %f\n",
                records[i].count, records[i].ticks, records[i].seconds);
    }
    fclose(file);
}

typedef enum { Beginning, Middle, End } position;
typedef enum { Get, Insert, Remove, Filter } operation;

void int_list_timing(record_t * records, position insert_pos,
                     int test_runs, int test_iterations,
                     size_t initial_count, int step_size, operation op)
{
    time_t t;
    unsigned int seed = time(&t);
    int test_num;
    for (test_num = 0; test_num < test_runs; test_num++) {
        srand(seed++);
        int_list_t list = int_list_random(initial_count + 1);
        int i;
        clock_t start = clock();
        for (i = 0; i < test_iterations; i++) {
            int pos;
            int obj;
            switch (insert_pos) {
            case Beginning:
                pos = 0;
                break;
            case Middle:
                pos = (initial_count) / 2;
                break;
            case End:
                pos = initial_count;
                break;
            default:
                printf("invalid position specification\n");
                exit(1);
            }
            switch (op) {
            case Get:
                obj = int_list_get(list, pos);
                break;
            case Insert:
                int_list_insert(list, pos, 0);
                break;
            case Remove:
                int_list_remove(list, pos);
                break;
            case Filter:
                int_list_filter(list, RAND_LIMIT / 2);
                break;
            default:
                printf("invalid operation specification\n");
                exit(1);
            }
        }
        clock_t end = clock();
        record_t record;
        record.count = (int) initial_count;
        record.ticks = (double) (end - start);
        record.seconds = (double) record.ticks / CLOCKS_PER_SEC;
        records[test_num] = record;
        initial_count += step_size;
        int_list_dispose(list);
        record_display(record);
    }
}


int main()
{
    int_list_t list = int_list_random(10);

    int test_runs = 8;
    int test_iterations = 1024;
    int initial_count = 4096;
    int step_size = 4096;

    HLINE;
    printf("List Get timing:\n");
    record_t list_get_start_records[test_runs];
    record_t list_get_middle_records[test_runs];
    record_t list_get_end_records[test_runs];

    HLINE;
    printf("  Beginning:\n");
    int_list_timing(list_get_start_records, Beginning, test_runs,
                    test_iterations, initial_count, step_size, Get);
    HLINE;
    printf("  Middle:\n");
    int_list_timing(list_get_middle_records, Middle, test_runs,
                    test_iterations, initial_count, step_size, Get);

    HLINE;
    printf("  End:\n");
    int_list_timing(list_get_end_records, End, test_runs,
                    test_iterations, initial_count, step_size, Get);


    HLINE;
    printf("List Insert timing:\n");
    record_t list_insert_start_records[test_runs];
    record_t list_insert_middle_records[test_runs];
    record_t list_insert_end_records[test_runs];

    HLINE;
    printf("  Beginning:\n");
    int_list_timing(list_insert_start_records, Beginning, test_runs,
                    test_iterations, initial_count, step_size, Insert);
    HLINE;
    printf("  Middle:\n");
    int_list_timing(list_insert_middle_records, Middle, test_runs,
                    test_iterations, initial_count, step_size, Insert);

    HLINE;
    printf("  End:\n");
    int_list_timing(list_insert_end_records, End, test_runs,
                    test_iterations, initial_count, step_size, Insert);



    HLINE;
    printf("List Remove timing:\n");
    record_t list_remove_start_records[test_runs];
    record_t list_remove_middle_records[test_runs];
    record_t list_remove_end_records[test_runs];

    HLINE;
    printf("  Beginning:\n");
    int_list_timing(list_remove_start_records, Beginning, test_runs,
                    test_iterations, initial_count, step_size, Remove);
    HLINE;
    printf("  Middle:\n");
    int_list_timing(list_remove_middle_records, Middle, test_runs,
                    test_iterations, initial_count, step_size, Remove);

    HLINE;
    printf("  End:\n");
    int_list_timing(list_remove_end_records, End, test_runs,
                    test_iterations, initial_count, step_size, Remove);



    HLINE;
    printf("List Filter timing:\n");
    record_t list_filter_records[test_runs];

    int_list_timing(list_filter_records, Beginning, test_runs,
                    test_iterations, initial_count, step_size, Filter);


    HLINE;

    printf("Tests complete. Generate CSV files from data? (y/n): ");
    /* char response = getchar(); */
    if (1 /* response == 'y' */ ) {
        write_data("list_get_start.csv", test_runs,
                   list_get_start_records);
        write_data("list_get_middle.csv", test_runs,
                   list_get_middle_records);
        write_data("list_get_end.csv", test_runs, list_get_end_records);

        write_data("list_insert_start.csv", test_runs,
                   list_insert_start_records);
        write_data("list_insert_middle.csv", test_runs,
                   list_insert_middle_records);
        write_data("list_insert_end.csv", test_runs,
                   list_insert_end_records);

        write_data("list_remove_start.csv", test_runs,
                   list_remove_start_records);
        write_data("list_remove_middle.csv", test_runs,
                   list_remove_middle_records);
        write_data("list_remove_end.csv", test_runs,
                   list_remove_end_records);

        write_data("list_filter.csv", test_runs, list_filter_records);
    }

    /* list_get_start_records[test_runs]; */
    /* record_t list_get_middle_records[test_runs]; */
    /* record_t list_get_end_records[test_runs]; */

    return 0;
}
