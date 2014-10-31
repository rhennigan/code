#include "array.h"
#include <time.h>
#include <stdio.h>
#include <stdlib.h>

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

void int_array_timing(record_t * records, position insert_pos,
                      int test_runs, int test_iterations,
                      size_t max_length, size_t initial_count,
                      int step_size, operation op)
{

    time_t t;
    unsigned int seed = time(&t);
    int test_num;
    for (test_num = 0; test_num < test_runs; test_num++) {

        srand(seed++);
        int_array_t *array = int_array_random(max_length, initial_count);

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
                pos = (initial_count + i) / 2;
                break;
            case End:
                pos = initial_count + i;
                break;
            default:
                printf("invalid position specification\n");
                exit(1);
            }

            switch (op) {
            case Get:
                obj = int_array_get(array, pos);
                break;
            case Insert:
                int_array_insert(array, pos, 0);
                break;
            case Remove:
                int_array_remove(array, pos);
                break;
            case Filter:
                int_array_filter(array, RAND_LIMIT / 2);
                break;
            default:
                printf("invalid operation specification\n");
                exit(1);
            }

        }
        clock_t end = clock();

        record_t record;
        record.count = (int) initial_count;
        record.ticks = (int) (end - start);
        record.seconds = (double) record.ticks / CLOCKS_PER_SEC;
        records[test_num] = record;

        initial_count += step_size;
        max_length += step_size;
        int_array_dispose(array);

        record_display(record);
    }
}

int main()
{
    int test_runs = 8;
    int test_iterations = 1024;
    int initial_count = 4096;
    int step_size = 4096;
    size_t max_length = initial_count + test_iterations;

    HLINE;
    printf("Array Get timing:\n");
    record_t array_get_start_records[test_runs];
    record_t array_get_middle_records[test_runs];
    record_t array_get_end_records[test_runs];

    HLINE;
    printf("  Beginning:\n");
    int_array_timing(array_get_start_records, Beginning, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Get);
    HLINE;
    printf("  Middle:\n");
    int_array_timing(array_get_middle_records, Middle, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Get);

    HLINE;
    printf("  End:\n");
    int_array_timing(array_get_end_records, End, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Get);

    HLINE;
    printf("Array Insert timing:\n");
    record_t array_insert_start_records[test_runs];
    record_t array_insert_middle_records[test_runs];
    record_t array_insert_end_records[test_runs];

    HLINE;
    printf("  Beginning:\n");
    int_array_timing(array_insert_start_records, Beginning, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Insert);

    HLINE;
    printf("  Middle:\n");
    int_array_timing(array_insert_middle_records, Middle, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Insert);

    HLINE;
    printf("  End:\n");
    int_array_timing(array_insert_end_records, End, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Insert);

    HLINE;
    printf("Array Remove timing:\n");
    record_t array_remove_start_records[test_runs];
    record_t array_remove_middle_records[test_runs];
    record_t array_remove_end_records[test_runs];

    HLINE;
    printf("  Beginning:\n");
    int_array_timing(array_remove_start_records, Beginning, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Remove);

    HLINE;
    printf("  Middle:\n");
    int_array_timing(array_remove_middle_records, Middle, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Remove);

    HLINE;
    printf("  End:\n");
    int_array_timing(array_remove_end_records, End, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Remove);

    HLINE;
    printf("Array Filter timing:\n");
    record_t array_filter_records[test_runs];

    int_array_timing(array_filter_records, Beginning, test_runs,
                     test_iterations, max_length, initial_count,
                     step_size, Filter);


    HLINE;

    printf("Tests complete. Generate CSV files from data? (y/n): ");
    /* char response = getchar(); */
    if (1 /* response == 'y' */ ) {
        write_data("array_get_start.csv", test_runs,
                   array_get_start_records);
        write_data("array_get_middle.csv", test_runs,
                   array_get_middle_records);
        write_data("array_get_end.csv", test_runs, array_get_end_records);

        write_data("array_insert_start.csv", test_runs,
                   array_insert_start_records);
        write_data("array_insert_middle.csv", test_runs,
                   array_insert_middle_records);
        write_data("array_insert_end.csv", test_runs,
                   array_insert_end_records);

        write_data("array_remove_start.csv", test_runs,
                   array_remove_start_records);
        write_data("array_remove_middle.csv", test_runs,
                   array_remove_middle_records);
        write_data("array_remove_end.csv", test_runs,
                   array_remove_end_records);

        write_data("array_filter.csv", test_runs, array_filter_records);
    }

    return 0;
}
