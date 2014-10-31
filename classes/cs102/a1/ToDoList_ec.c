#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define BufferSize 512
#define MaxTaskSize 62

typedef struct {
    int priority;
    char desc[MaxTaskSize + 1];
} Task;

const Task NULL_TASK = { -1, "" };

typedef struct TaskList {
  Task head;
  struct TaskList *tail;
} TaskList;

TaskList *cons(Task head, TaskList *tail) {
    TaskList *list = malloc(sizeof(TaskList));
    list->head = head;
    list->tail = tail;
    return list;
}

Task nth(TaskList *tasks, int n) {
    return (n && tasks) ? (nth(tasks->tail, n - 1)) : (tasks->head);
}

TaskList *append(TaskList *xs, TaskList *ys) {
    return (!xs) ? ys : cons(xs->head, append(xs->tail, ys));
}

TaskList *removeTask(TaskList *acc, TaskList *tasks, int n) {
    if (n && tasks) {
        return removeTask(cons(tasks->head, acc), tasks->tail, n - 1);
    }
    else {
        return append(acc, tasks->tail);
    }
}

TaskList *replace(TaskList *acc, TaskList *tasks, int n, Task task) {
    if (n && tasks) {
        return replace(cons(tasks->head, acc), tasks->tail, n - 1, task);
    }
    else {
        return append(acc, cons(task, tasks->tail));
    }
}

void printTask(Task task, int taskNum) {
    printf("  %d      %d       %s\n", taskNum + 1, task.priority, task.desc);
}

void printNthTask(TaskList *tasks, int taskNum) {
    Task task = nth(tasks, taskNum);
    printTask(task, taskNum);
}

void printAllTasks(TaskList *tasks, int taskNumOffset) {
    if (tasks) {
        printTask(tasks->head, taskNumOffset);
        printAllTasks(tasks->tail, taskNumOffset + 1);
    }
}

TaskList *filterLeft(Task task, TaskList *tasks) {
    if (tasks) {
        if (tasks->head.priority <= task.priority) {
            return cons(tasks->head, filterLeft(task, tasks->tail));
        }
        else {
            return filterLeft(task, tasks->tail);
        }
    }
    else {
        return NULL;
    }
}

TaskList *filterRight(Task task, TaskList *tasks) {
    if (tasks) {
        if (tasks->head.priority > task.priority) {
            return cons(tasks->head, filterRight(task, tasks->tail));
        }
        else {
            return filterRight(task, tasks->tail);
        }
    }
    else {
        return NULL;
    }
}

TaskList *quickSort(TaskList *tasks) {
    if (!tasks) { 
        return NULL;
    }
    if (tasks->tail == NULL) {
        return tasks;
    }
    else {
        TaskList *left = quickSort(filterLeft(tasks->head, tasks->tail));
        TaskList *right = quickSort(filterRight(tasks->head, tasks->tail));
        
        return (append(left, cons(tasks->head, right)));
    }
}

int listLength(TaskList *list) {
    if (!list) return 0;
    return (1 + listLength(list->tail));
}

TaskList *reverseRec(TaskList *list, TaskList *acc) {
    return (!list) ? acc : (reverseRec(list->tail, cons(list->head, acc)));
}

TaskList *reverse(TaskList *list) {
    return reverseRec(list, NULL);
}

void dispose(TaskList *list) {
    if (list) {
        dispose(list->tail);
        free(list);
        list = NULL;
    }
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

void getString(char *string) {
    fgets(string, MaxTaskSize, stdin);
    removeNewline(string, MaxTaskSize);
    fflush(stdin);
}

Task loadTask(FILE *in) {
    char line[BufferSize];
    if (fgets(line, BufferSize, in) != NULL) {
        Task task;
        task.priority = line[0] - '0';
        int i;
        char ch;
        for (i = 0; i < MaxTaskSize; i++)
        {
            ch = line[i + 2];
            if ((ch == '\n') || (ch == EOF)) {
                task.desc[i] = '\0';
                return task;
            }
            else {
                task.desc[i] = ch;
            }
        }
        task.desc[MaxTaskSize] = '\0';
        return task;
    }
    else {
        return NULL_TASK;
    }
}

int isNullTask(Task task) {
    return task.priority == -1;
}

TaskList *loadTasks() {
    char fileName[BufferSize];
    TaskList *tasks = NULL;

    printf("Enter input filename: ");
    getString(fileName);
    FILE *in = fopen(fileName, "r");

    Task task = loadTask(in);

    while (!isNullTask(task)) {
        tasks = cons(task, tasks);
        task = loadTask(in);
    }

    fclose(in);

    return quickSort(tasks);
}

void saveTask(FILE *out, Task task) {
    int i;
    char line[BufferSize];

    line[0] = task.priority + '0';
    line[1] = '\t';

    for (i = 2; i < BufferSize - 1; i++) {
        if (task.desc[i - 2] == '\0') {
            line[i] = '\n';
            line[i + 1] = '\0';
            break;
        }
        else {
            line[i] = task.desc[i - 2];
        }
    }
    fputs(line, out);
}

void saveTasksRec(FILE *out, TaskList *tasks) {
    if (tasks) {
        saveTask(out, tasks->head);
        saveTasksRec(out, tasks->tail);
    }
}

void saveTasks(TaskList *tasks) {
    char fileName[BufferSize];
    printf("Enter output filename: ");
    getString(fileName);
    FILE *out = fopen(fileName, "w");
    saveTasksRec(out, tasks);
    fclose(out);
}

void menu() {
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

void menuDisplayOneTask(TaskList *tasks) {
    int taskNum;
    int taskCount = listLength(tasks);

    printf("There are currently %d tasks. Please select a task number (1-%d): ", taskCount, taskCount);
    taskNum = getNumber(1, taskCount) - 1;

    printf("--------------------------------------------------------------------------------\n");
    printf("| # | Priority | Description                                                   |\n");
    printf("--------------------------------------------------------------------------------\n");
    printNthTask(tasks, taskNum);
    printf("--------------------------------------------------------------------------------\n");
}

void menuDisplayAllTasks(TaskList *tasks) {
    printf("--------------------------------------------------------------------------------\n");
    printf("| # | Priority | Description                                                   |\n");
    printf("--------------------------------------------------------------------------------\n");
    printAllTasks(tasks, 0);
    printf("--------------------------------------------------------------------------------\n");
    printf("\n");
}

TaskList *menuInsertTask(TaskList *tasks) {
    Task newTask;
    
    printf("Please enter a description for the new task: ");
    getString(newTask.desc);

    printf("Please enter a priority number (1-9): ");
    newTask.priority = getNumber(1, 9);
    
    tasks = quickSort(cons(newTask, tasks));

    menuDisplayAllTasks(tasks);

    return tasks;
}

TaskList *menuRemoveTask(TaskList *tasks) {
    int taskNum;
    int taskCount = listLength(tasks);

    menuDisplayAllTasks(tasks);

    printf("Please select a task number for removal (1-%d): ", taskCount);
    taskNum = getNumber(1, taskCount--) - 1;

    tasks = quickSort(removeTask(NULL, tasks, taskNum));

    menuDisplayAllTasks(tasks);

    return tasks;
}

TaskList *menuReplaceTask(TaskList *tasks) {
    int taskNum;
    int taskCount = listLength(tasks);
    Task newTask;

    menuDisplayAllTasks(tasks);

    printf("Please select a task number for replacement (1-%d): ", taskCount);
    taskNum = getNumber(1, taskCount) - 1;

    printf("Please enter a description for the new task: ");
    getString(newTask.desc);

    printf("Please enter a priority number (1-9): ");
    newTask.priority = getNumber(1, 9);

    tasks = quickSort(replace(NULL, tasks, taskNum, newTask));

    menuDisplayAllTasks(tasks);

    return tasks;
}

TaskList *menuChangePriority(TaskList *tasks) {
    int taskNum;
    int taskCount = listLength(tasks);
    Task newTask;

    menuDisplayAllTasks(tasks);

    printf("Please select a task number to change (1-%d): ", taskCount);
    taskNum = getNumber(1, taskCount) - 1;
    newTask = nth(tasks, taskNum);

    printf("Please enter a priority number (1-9): ");
    newTask.priority = getNumber(1, 9);
    
    tasks = quickSort(replace(NULL, tasks, taskNum, newTask));

    menuDisplayAllTasks(tasks);

    return tasks;
}

int menuQuit(TaskList *tasks) {
    printf("Saving tasks...\n");
    saveTasks(tasks);
    printf("Tasks saved.\n");
    printf("Quitting...\n");
    dispose(tasks);
    exit(0);
}

int main() {
  TaskList *tasks = loadTasks();
  int selection = 0;
  
  menu();
  
  while (1) {
    selection = getUserSelection();
    printf("\n");
    switch (selection) {
      case 0:
        menu();
        break;
      case 1:
        menuDisplayOneTask(tasks);
        break;
      case 2:
        menuDisplayAllTasks(tasks);
        break;
      case 3:
        tasks = menuInsertTask(tasks);
        break;
      case 4:
        tasks = menuRemoveTask(tasks);
        break;
      case 5:
        tasks = menuReplaceTask(tasks);
        break;
      case 6:
        tasks = menuChangePriority(tasks);
        break;
      case 7:
        menuQuit(tasks);
      default:
        printf("Invalid option.");
        break;
    }
    printf("\n");
  };
  
  return 0;
}
