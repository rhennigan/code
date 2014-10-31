#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BufferSize 512
#define MaxTaskSize 62
#define MaxTasks 256

typedef struct {
    int priority;
    char desc[MaxTaskSize + 1];
} Task;

int exponentiation(int base, unsigned int exponent) {
    int i, result = 1;
    for (i = 0; i < exponent; i++)
        result *= base;
    return result;
}

void removeNewline(char *string, int size)
{
    int i;
    for (i = 0; i < size; ++i) {
        if (string[i] == '\n') {
            string[i] = '\0';
            return;
        }
    }
}

int getNumber(int low, int high) {
    char bufferIn[BufferSize];
    int bufferOut[BufferSize];
    int digit, number, exponent;

    while (1) {
        digit = 0;
        number = 0;
        exponent = 1;

        fgets(bufferIn, BufferSize, stdin);
        fflush(stdin);

        int i = 0, j = 0, k = 0;

        for (i = 0; i < BufferSize; i++) {
            if (bufferIn[i] == '\n') break;
            digit = bufferIn[i] - '0';
            if ((0 <= digit) && (digit <= 9)) {
                bufferOut[j++] = digit;
            }
        }

        for (k = j - 1; k >= 0; k--) {
            number += exponent * bufferOut[k];
            exponent *= 10;
        }

        if ((low <= number) && (number <= high)) {
            break;
        }
        else {
            printf("Invalid input. Please enter a number between %d and %d: ", low, high);
        }
    }

    return number;
}

void *getString(char *string) {
    fgets(string, MaxTaskSize, stdin);
    removeNewline(string, MaxTaskSize);
    fflush(stdin);
}

int loadTasks(Task *tasks) {
    char fileName[BufferSize];
    char line[BufferSize];

    printf("Enter input filename: ");
    getString(fileName);

    FILE *in = fopen(fileName, "r");

    int i = 0, j = 0;

    while (fgets(line, BufferSize, in) != NULL) {
        tasks[i].priority = line[0] - '0';
        for (j = 2; j < MaxTaskSize; j++) {
            if ((line[j] == '\n') || (line[j] == EOF)) {
                tasks[i].desc[j - 2] = '\0';
                break;
            }
            else {
                tasks[i].desc[j - 2] = line[j];
            }
        }
        i++;
    }

    fclose(in);

    return i;
}

void saveTasks(Task *tasks, int taskCount) {
    char fileName[BufferSize];
    char line[BufferSize];

    printf("Enter output filename: ");
    getString(fileName);

    FILE *out = fopen(fileName, "w");

    int i, j;
    for (i = 0; i < taskCount; i++) {
        line[0] = tasks[i].priority + '0';
        line[1] = '\t';
        for (j = 2; j < BufferSize - 1; j++) {
            if (tasks[i].desc[j - 2] == '\0') {
                line[j] = '\n';
                line[j + 1] = '\0';
                break;
            }
            else {
                line[j] = tasks[i].desc[j - 2];
            }
        }
        fputs(line, out);
    }

    fclose(out);
}

void insertionSort(Task *tasks, int taskCount) {
    Task hold;
    int i, j;
    for (i = 1; i < taskCount; i++) {
        hold = tasks[i];
        j = i - 1;
        while (j >= 0 && hold.priority < tasks[j].priority) {
            tasks[j + 1] = tasks[j];
            j = j - 1;
        }
        tasks[j + 1] = hold;
    }
}

void displayMenu() {
    printf("\n");
    printf("--------------------------------------------------------------------------------\n");
    printf("| To Do List -- Main Menu                                                      |\n");
    printf("--------------------------------------------------------------------------------\n");
    printf("| # | Description                                                              |\n");
    printf("--------------------------------------------------------------------------------\n");
    printf("  0   Display this menu.                                                        \n");
    printf("  1   Display a single task.                                                    \n");
    printf("  2   Display all tasks.                                                        \n");
    printf("  3   Add a new task.                                                           \n");
    printf("  4   Remove a task.                                                            \n");
    printf("  5   Replace a task.                                                           \n");
    printf("  6   Move a task to another location.                                          \n");
    printf("  7   Quit.                                                                     \n");
    printf("--------------------------------------------------------------------------------\n");
}

int getUserSelection() {
    printf("Select a menu option (0-7): ");
    return getNumber(0, 7);
}

void displayOneTask(Task *tasks, int taskCount) {
    int taskNum;

    printf("There are currently %d tasks. Please select a task number (1-%d): ", taskCount, taskCount);
    taskNum = getNumber(1, taskCount) - 1;

    printf("--------------------------------------------------------------------------------\n");
    printf("| # | Priority | Description                                                   |\n");
    printf("--------------------------------------------------------------------------------\n");
    printf("  %d      %d       %s\n", taskNum + 1, tasks[taskNum].priority, tasks[taskNum].desc);
    printf("--------------------------------------------------------------------------------\n");
}

void displayAllTasks(Task *tasks, int taskCount) {
    printf("--------------------------------------------------------------------------------\n");
    printf("| # | Priority | Description                                                   |\n");
    printf("--------------------------------------------------------------------------------\n");

    int i;
    for (i = 0; i < taskCount; i++) {
        int sl = strlen(tasks[i].desc);
        printf("  %d      %d       %s\n", i+1, tasks[i].priority, tasks[i].desc);
    }

    printf("--------------------------------------------------------------------------------\n");
    printf("\n");
}

int insertTask(Task *tasks, int taskCount) {
    Task newTask;

    if (taskCount == MaxTasks) {
        printf("Too many tasks.");
        exit(1);
    }

    printf("Please enter a description for the new task: ");
    getString(newTask.desc);

    printf("Please enter a priority number (1-9): ");
    newTask.priority = getNumber(1, 9);
    
    tasks[taskCount++] = newTask;
    insertionSort(tasks, taskCount);

    displayAllTasks(tasks, taskCount);

    return taskCount;
}

int removeTask(Task *tasks, int taskCount) {
    int taskNum, i;

    displayAllTasks(tasks, taskCount);

    printf("Please select a task number for removal (1-%d): ", taskCount);
    taskNum = getNumber(1, taskCount--) - 1;

    for (i = taskNum; i < taskCount; i++) {
        tasks[i] = tasks[i + 1];
    }

    displayAllTasks(tasks, taskCount);

    return taskCount;
}

void replaceTask(Task *tasks, int taskCount) {
    int taskNum;

    displayAllTasks(tasks, taskCount);

    printf("Please select a task number for replacement (1-%d): ", taskCount);
    taskNum = getNumber(1, taskCount) - 1;

    printf("Please enter a description for the new task: ");
    getString(tasks[taskNum].desc);

    printf("Please enter a priority number (1-9): ");
    tasks[taskNum].priority = getNumber(1, 9);

    insertionSort(tasks, taskCount);

    displayAllTasks(tasks, taskCount);
}

void changePriority(Task *tasks, int taskCount) {
    int taskNum;

    displayAllTasks(tasks, taskCount);

    printf("Please select a task number to change (1-%d): ", taskCount);
    taskNum = getNumber(1, taskCount) - 1;

    printf("Please enter a priority number (1-9): ");
    tasks[taskNum].priority = getNumber(1, 9);
    
    insertionSort(tasks, taskCount);

    displayAllTasks(tasks, taskCount);
}

int quit(Task *tasks, int taskCount) {
    printf("Saving tasks...\n");
    saveTasks(tasks, taskCount);
    printf("Tasks saved.\n");
    printf("Quitting...\n");
    exit(0);
}

int main() {
    Task tasks[MaxTasks];
    int taskCount = loadTasks(tasks);
    int selection = 0;

    insertionSort(tasks, taskCount);

    displayMenu();
    
    while (1) {
        selection = getUserSelection();
        printf("\n");
        switch (selection) {
        case 0:
            displayMenu();
            break;
        case 1:
            displayOneTask(tasks, taskCount);
            break;
        case 2:
            displayAllTasks(tasks, taskCount);
            break;
        case 3:
            taskCount = insertTask(tasks, taskCount);
            break;
        case 4:
            taskCount = removeTask(tasks, taskCount);
            break;
        case 5:
            replaceTask(tasks, taskCount);
            break;
        case 6:
            changePriority(tasks, taskCount);
            break;
        case 7:
            quit(tasks, taskCount);
        default:
            printf("Invalid option.");
            break;
        }
        printf("\n");
    };
    
    return 0;
}
