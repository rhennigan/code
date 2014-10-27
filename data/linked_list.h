/*
 *******************************************************************************
 * linked_list.h
 * Richard Hennigan
 * Thu Oct 2 21:09:02 EDT 2014
 *
 * Types:
 *   TYPE_list_t - polymorphic linked list
 *
 * Functions:
 *   +> T1_T2_list_map()
 *   +> T1_T2_list_zip()
 *   +> T1_T2_T3_list_zipwith()
 *   +> TYPE_list_app()
 *   +> TYPE_list_append()
 *   +> TYPE_list_cons()
 *   +> TYPE_list_copy()
 *   +> TYPE_list_count()
 *   +> TYPE_list_delete()
 *   +> TYPE_list_dispose()
 *   +> TYPE_list_filter()
 *   +> TYPE_list_find()
 *   +> TYPE_list_init()
 *   +> TYPE_list_insert()
 *   +> TYPE_list_insertat()
 *   +> TYPE_list_iter()
 *   +> TYPE_list_length()
 *   +> TYPE_list_print()
 *   +> TYPE_list_range()
 *   +> TYPE_list_remove()
 *   +> TYPE_list_reverse()
 *
 ******************************************************************************/

#ifndef _LIB_DATA_LINKED_LIST_H
#define _LIB_DATA_LINKED_LIST_H

#include <stdlib.h>
#include <stdio.h>
#include <assert.h>
#include <stdbool.h>

#ifndef EMPTY
#define EMPTY NULL
#endif

#define DEF_LIST_TYPE(TYPE)                                                    \
  typedef struct TYPE##_list_s                                                 \
  {                                                                            \
    TYPE head;                                                                 \
    struct TYPE##_list_s *tail;                                                \
  } TYPE##_list_t;



/*******************************************************************************
 * function:    Length
 * signature:   T_list_t* → Int
 * persistence: True
 * performance: O(n)
 * description: Returns the number of items in the list
 ******************************************************************************/
#define DEF_LIST_LENGTH(TYPE)                                                  \
  int                                                                          \
  TYPE##_list_length(TYPE##_list_t * list)                                     \
  {                                                                            \
    int len = 0;                                                               \
    TYPE##_list_t *current = list;                                             \
                                                                               \
    while (current)                                                            \
      {                                                                        \
        len += 1;                                                              \
        current = current->tail;                                               \
      }                                                                        \
                                                                               \
    return len;                                                                \
  }



/*******************************************************************************
 * function:    Find
 * signature:   T_list* × T × (T × T → Bool) → Bool
 * persistence: True
 * performance: O(n)
 * description: Returns true if obj is present in the list and false otherwise.
 ******************************************************************************/
#define DEF_LIST_FIND(TYPE)                                                    \
  bool                                                                         \
  TYPE##_list_find (TYPE##_list_t * list, TYPE data, bool (*cmp) (TYPE, TYPE)) \
  {                                                                            \
    TYPE##_list_t *current = list;                                             \
                                                                               \
    while (current)                                                            \
      {                                                                        \
        if ((*cmp)(current->head, data))                                       \
          {                                                                    \
            return true;                                                       \
          }                                                                    \
        current = current->tail;                                               \
      }                                                                        \
                                                                               \
    return false;                                                              \
  }



/*******************************************************************************
 * function:    Count
 * signature:   T_list* × T× (T × T → Bool) → Int
 * persistence: True
 * performance: O(n)
 * description: Returns the number of times that obj appears in the list.
 ******************************************************************************/
#define DEF_LIST_COUNT(TYPE)                                                   \
  int                                                                          \
  TYPE##_list_count (TYPE##_list_t * list, TYPE data, bool (*cmp) (TYPE, TYPE))\
  {                                                                            \
    int count = 0;                                                             \
    TYPE##_list_t *current = list;                                             \
                                                                               \
    while (current)                                                            \
      {                                                                        \
        count = ((*cmp)(current->head, data)) ? count + 1 : count;             \
        current = current->tail;                                               \
      }                                                                        \
                                                                               \
    return count;                                                              \
  }



/*******************************************************************************
 * function:    Dispose List
 * signature:   T_list** → Unit
 * persistence: False
 * performance: O(n)
 * description: Releases the memory that was allocated for the list.
 ******************************************************************************/
#define DEF_LIST_DISPOSE(TYPE)                                                 \
  void                                                                         \
  TYPE##_list_dispose (TYPE##_list_t ** list)                                  \
  {                                                                            \
    TYPE##_list_t *current = (*list);                                          \
    TYPE##_list_t *next = current;                                             \
    while (current)                                                            \
      {                                                                        \
        next = current->tail;                                                  \
        free (current);                                                        \
        current = next;                                                        \
      }                                                                        \
    (*list) = EMPTY;                                                           \
  }



/*******************************************************************************
 * function:    Initialize List
 * signature:   T → T_list*
 * persistence: True
 * performance: O(1)
 * description: Creates a list with a single element.
 ******************************************************************************/
#define DEF_LIST_INIT(TYPE)                                                    \
  TYPE##_list_t *                                                              \
  TYPE##_list_init (TYPE data)                                                 \
  {                                                                            \
    TYPE##_list_t *new_list = (TYPE##_list_t*) malloc (sizeof (TYPE##_list_t));\
    assert (new_list);                                                         \
    new_list->head = data;                                                     \
    new_list->tail = EMPTY;                                                    \
    return new_list;                                                           \
  }



/*******************************************************************************
 * function:    Add to End
 * signature:   T_list* × T → T_list*
 * persistence: False
 * performance: O(1)
 * description: Adds a single element to the end of the list.
 ******************************************************************************/
#define DEF_LIST_APP(TYPE)                                                     \
  TYPE##_list_t *                                                              \
  TYPE##_list_app (TYPE##_list_t * list, TYPE head)                            \
  {                                                                            \
    TYPE##_list_t *new_node = TYPE##_list_init (head);                         \
    TYPE##_list_t *current = list;                                             \
    TYPE##_list_t *prev = list;                                                \
    while (current)                                                            \
      {                                                                        \
        prev = current;                                                        \
        current = current->tail;                                               \
      }                                                                        \
    prev->tail = new_node;                                                     \
    return list;                                                               \
  }



/*******************************************************************************
 * function:    Add to Beginning
 * signature:   T_list* × T → T_list*
 * persistence: False
 * performance: O(1)
 * description: Adds a single element to the beginning of the list.
 ******************************************************************************/
#define DEF_LIST_CONS(TYPE)                                                    \
  TYPE##_list_t *                                                              \
  TYPE##_list_cons (TYPE##_list_t * list, TYPE head)                           \
  {                                                                            \
    TYPE##_list_t *new_list = (TYPE##_list_t*) malloc (sizeof (TYPE##_list_t));\
    assert (new_list);                                                         \
    new_list->head = head;                                                     \
    new_list->tail = list;                                                     \
    return new_list;                                                           \
  }



/*******************************************************************************
 * function:    Copy
 * signature:   T_list* → T_list*
 * persistence: True
 * performance: O(n)
 * description: Returns a copy of the input list.
 ******************************************************************************/
#define DEF_LIST_COPY(TYPE)                                                    \
  TYPE##_list_t *                                                              \
  TYPE##_list_copy (TYPE##_list_t * list)                                      \
  {                                                                            \
    if (list == EMPTY)                                                         \
      {                                                                        \
        return EMPTY;                                                          \
      }                                                                        \
    else                                                                       \
      {                                                                        \
        TYPE##_list_t *current = list->tail;                                   \
        TYPE##_list_t *new_list = TYPE##_list_init (list->head);               \
        TYPE##_list_t *new_current = new_list;                                 \
        while (current)                                                        \
          {                                                                    \
            new_current->tail = TYPE##_list_init (current->head);              \
            current = current->tail;                                           \
            new_current = new_current->tail;                                   \
          }                                                                    \
        return new_list;                                                       \
      }                                                                        \
  }




/*******************************************************************************
 * function:    Add to Beginning
 * signature:   T_list* × T → T_list*
 * persistence: True
 * performance: O(n)
 * description: Adds a single element to the beginning of a copy of the list.
 *              The input list is unchanged.
 ******************************************************************************/
#define DEF_LIST_INSERT(TYPE)                                                  \
  TYPE##_list_t *                                                              \
  TYPE##_list_insert (TYPE##_list_t * list, TYPE data)                         \
  {                                                                            \
    TYPE##_list_t *new_list = TYPE##_list_copy (list);                         \
    new_list = TYPE##_list_cons (new_list, data);                              \
    return new_list;                                                           \
  }



/*******************************************************************************
 * function:    Add at Location
 * signature:   T_list* × T × Int → T_list*
 * persistence: True
 * performance: O(n)
 * description: Adds a single element at an indexed location of a copy of the
 *              list. The input list is unchanged.
 ******************************************************************************/
#define DEF_LIST_INSERTAT(TYPE)                                                \
  TYPE##_list_t *                                                              \
  TYPE##_list_insertat (TYPE##_list_t * list, TYPE data, int position)         \
  {                                                                            \
    assert (position >= 0);                                                    \
    if (position == 0)                                                         \
      {                                                                        \
        return TYPE##_list_insert (list, data);                                \
      }                                                                        \
    else                                                                       \
      {                                                                        \
        TYPE##_list_t *new_list = TYPE##_list_copy (list);                     \
        TYPE##_list_t *node = TYPE##_list_init (data);                         \
        TYPE##_list_t *current = new_list;                                     \
        TYPE##_list_t *prev = new_list;                                        \
        int i;                                                                 \
        for (i = position; i > 0 && current; i--)                              \
          {                                                                    \
            prev = current;                                                    \
            current = current->tail;                                           \
          }                                                                    \
        assert (i < 1);                                                        \
        prev->tail = node;                                                     \
        node->tail = current;                                                  \
        return new_list;                                                       \
      }                                                                        \
  }



/*******************************************************************************
 * function:    Delete
 * signature:   T_list* → T_list*
 * persistence: True
 * performance: O(n)
 * description: Returns a copy of the input list with the first element removed.
 *              The input list is unchanged.
 ******************************************************************************/
#define DEF_LIST_DELETE(TYPE)                                                  \
  TYPE##_list_t *                                                              \
  TYPE##_list_delete (TYPE##_list_t * list)                                    \
  {                                                                            \
    TYPE##_list_t *new_list = TYPE##_list_copy (list->tail);                   \
    return new_list;                                                           \
  }



/*******************************************************************************
 * function:    Delete at Location
 * signature:   T_list* × Int → T_list*
 * persistence: True
 * performance: O(n)
 * description: Returns a copy of the input list with the nth element removed.
 ******************************************************************************/
#define DEF_LIST_DELETEAT(TYPE)                                                \
  TYPE##_list_t *                                                              \
  TYPE##_list_deleteat (TYPE##_list_t * list, int position)                    \
  {                                                                            \
    assert (position >= 0);                                                    \
                                                                               \
    TYPE##_list_t *new_list = TYPE##_list_copy (list);                         \
    TYPE##_list_t *junk = EMPTY;                                               \
                                                                               \
    if (position == 0)                                                         \
      {                                                                        \
        junk = new_list;                                                       \
        new_list = new_list->tail;                                             \
        free (junk);                                                           \
        return new_list;                                                       \
      }                                                                        \
                                                                               \
    else                                                                       \
      {                                                                        \
        TYPE##_list_t *current = new_list;                                     \
                                                                               \
        int i;                                                                 \
        for (i = position; i > 1 && current; i--)                              \
          {                                                                    \
            current = current->tail;                                           \
          }                                                                    \
        assert (current);                                                      \
        junk = current->tail;                                                  \
        assert (junk);                                                         \
        current->tail = junk->tail;                                            \
        free (junk);                                                           \
        return new_list;                                                       \
      }                                                                        \
  }




/*******************************************************************************
 * function:    Iterate
 * signature:   T_list* × (T → Unit) → Unit
 * persistence: True
 * performance: O(n)
 * description: Applies the given function to each element of the list.
 ******************************************************************************/
#define DEF_LIST_ITER(TYPE)                                                    \
  void                                                                         \
  TYPE##_list_iter (TYPE##_list_t * list, void (*f) (TYPE))                    \
  {                                                                            \
    TYPE##_list_t *current = list;                                             \
                                                                               \
    while (current != EMPTY)                                                   \
      {                                                                        \
        (*f) (current->head);                                                  \
        current = current->tail;                                               \
      }                                                                        \
                                                                               \
    return;                                                                    \
  }



/*******************************************************************************
 * function:    Map
 * signature:   T1_clist* × (T1 → T2) → T2_clist*
 * persistence: True
 * performance: O(n)
 * description: Applies the given function to each element of the list and
 *              returns the list of results.
 ******************************************************************************/
#define DEF_LIST_MAP(T1, T2)                                                   \
  T2##_list_t *                                                                \
  T1##_##T2##_list_map (T1##_list_t * list, T2 (*f) (T1))                      \
  {                                                                            \
    if (list == EMPTY)                                                         \
      {                                                                        \
        return EMPTY;                                                          \
      }                                                                        \
                                                                               \
    else                                                                       \
      {                                                                        \
        T2##_list_t *new_list = T2##_list_init ((*f) (list->head));            \
        T2##_list_t *new_node = new_list;                                      \
        T1##_list_t *current = list->tail;                                     \
                                                                               \
        while (current != EMPTY)                                               \
          {                                                                    \
            new_node->tail = T2##_list_init ((*f) (current->head));            \
            new_node = new_node->tail;                                         \
            current = current->tail;                                           \
          }                                                                    \
                                                                               \
        return new_list;                                                       \
      }                                                                        \
  }



/*******************************************************************************
 * function:    Zip
 * signature:   T1_list* × T2_list* → (T1 × T2)_list*
 * persistence: True
 * performance: O(n)
 * description: Creates a list of tuples, where the nth tuple is composed of the
 *              nth element from the first list as its first item, and the nth
 *              element from the second list as its second item. If the two
 *              lists are different sizes, the extra elements at the end of the
 *              larger list will be discarded.
 ******************************************************************************/
#define DEF_LIST_ZIP(T1, T2)                                                   \
  T1##_##T2##_tuple_t_list_t *                                                 \
  T1##_##T2##_list_zip (T1##_list_t * list1, T2##_list_t * list2)              \
  {                                                                            \
    if (list1 == EMPTY || list2 == EMPTY)                                      \
      {                                                                        \
        return EMPTY;                                                          \
      }                                                                        \
                                                                               \
    else                                                                       \
      {                                                                        \
        T1##_##T2##_tuple_t_list_t * new_list, * new_current;                  \
        T1##_##T2##_tuple_t tuple = (T1##_##T2##_tuple_t)                      \
          { list1->head, list2->head };                                        \
        new_list = T1##_##T2##_tuple_t_list_init(tuple);                       \
        new_current = new_list;                                                \
        T1##_list_t * current1 = list1->tail;                                  \
        T2##_list_t * current2 = list2->tail;                                  \
                                                                               \
        while (current1 != EMPTY && current2 != EMPTY)                         \
          {                                                                    \
            tuple = (T1##_##T2##_tuple_t)                                      \
              { current1->head, current2->head };                              \
            new_current->tail = T1##_##T2##_tuple_t_list_init(tuple);          \
            new_current = new_current->tail;                                   \
            current1 = current1->tail;                                         \
            current2 = current2->tail;                                         \
          }                                                                    \
                                                                               \
        return new_list;                                                       \
      }                                                                        \
  }



/*******************************************************************************
 * function:    Zipwith
 * signature:   T1_list* × T2_list* × (T1 × T2 → T3) → T3_list*
 * persistence: True
 * performance: O(n)
 * description: Simultaneously zips two lists together and maps a given
 *              function over the results to yield a new list of a new type.
 ******************************************************************************/
#define DEF_LIST_ZIPWITH(T1, T2, T3)                                           \
  T3##_list_t *                                                                \
  T1##_##T2##_##T3##_list_zipwith (T1##_list_t * list1, T2##_list_t * list2,   \
                                   T3 (*f) (T1, T2))                           \
  {                                                                            \
    if (list1 == EMPTY || list2 == EMPTY)                                      \
      {                                                                        \
        return EMPTY;                                                          \
      }                                                                        \
                                                                               \
    else                                                                       \
      {                                                                        \
        T3##_list_t *new_list, *new_current;                                   \
        new_list = T3##_list_init ((*f) (list1->head, list2->head));           \
        new_current = new_list;                                                \
        T1##_list_t *current1 = list1->tail;                                   \
        T2##_list_t *current2 = list2->tail;                                   \
                                                                               \
        while (current1 != EMPTY && current2 != EMPTY)                         \
          {                                                                    \
            T3 obj = (*f) (current1->head, current2->head);                    \
            new_current->tail = T3##_list_init (obj);                          \
            new_current = new_current->tail;                                   \
            current1 = current1->tail;                                         \
            current2 = current2->tail;                                         \
          }                                                                    \
                                                                               \
        return new_list;                                                       \
      }                                                                        \
  }



/*******************************************************************************
 * function:    Reverse
 * signature:   T_list* × T → T_list*
 * persistence: False
 * performance: O(n)
 * description: Returns a reversed copy of the input list.
 ******************************************************************************/
#define DEF_LIST_REVERSE(TYPE)                                                 \
  TYPE##_list_t *                                                              \
  TYPE##_list_reverse (TYPE##_list_t * list)                                   \
  {                                                                            \
    TYPE##_list_t *reversed_list = EMPTY;                                      \
    TYPE##_list_t *current = list;                                             \
                                                                               \
    while (current)                                                            \
      {                                                                        \
        reversed_list = TYPE##_list_cons (reversed_list, current->head);       \
        current = current->tail;                                               \
      }                                                                        \
                                                                               \
    return reversed_list;                                                      \
  }



/*******************************************************************************
 * function:    Filter
 * signature:   T_list* × T × (T × T → Bool) → T_list*
 * persistence: True
 * performance: O(n)
 * description: Returns a copy of the input list with all instances of obj
 *              deleted. The input list is unchanged. (*cmp) is a pointer to a
 *              function that determines when two objects of type T are equal.
 ******************************************************************************/
#define DEF_LIST_FILTER(TYPE)                                                  \
  TYPE##_list_t *                                                              \
  TYPE##_list_filter (TYPE##_list_t * list, TYPE obj, bool (*cmp) (TYPE, TYPE))\
  {                                                                            \
    if (list == EMPTY)                                                         \
      {                                                                        \
        return EMPTY;                                                          \
      }                                                                        \
                                                                               \
    else                                                                       \
      {                                                                        \
        TYPE##_list_t *current = list;                                         \
                                                                               \
        while ((*cmp) (current->head, obj))                                    \
          {                                                                    \
            current = current->tail;                                           \
                                                                               \
            if (current == EMPTY)                                              \
              {                                                                \
                return EMPTY;                                                  \
              }                                                                \
          }                                                                    \
                                                                               \
        TYPE##_list_t *new_list = TYPE##_list_init (current->head);            \
        TYPE##_list_t *new_node = new_list;                                    \
        current = current->tail;                                               \
                                                                               \
        while (current != EMPTY)                                               \
          {                                                                    \
            if (!(*cmp) (current->head, obj))                                  \
              {                                                                \
                new_node->tail = TYPE##_list_init (current->head);             \
                new_node = new_node->tail;                                     \
              }                                                                \
                                                                               \
            current = current->tail;                                           \
          }                                                                    \
                                                                               \
        return new_list;                                                       \
      }                                                                        \
  }



/*******************************************************************************
 * function:    Append
 * signature:   T_list* × T_list* → T_list*
 * persistence: True
 * performance: O(n)
 * description: Joins two  lists into one, where the first element is
 *              the first element of list1, and the last element is the last
 *              element of list2.  The input lists are unchanged.
 ******************************************************************************/
#define DEF_LIST_APPEND(TYPE)                                                  \
  TYPE##_list_t *                                                              \
  TYPE##_list_append (TYPE##_list_t * list1, TYPE##_list_t * list2)            \
  {                                                                            \
    TYPE##_list_t *new_list1 = TYPE##_list_copy (list1);                       \
    TYPE##_list_t *new_list2 = TYPE##_list_copy (list2);                       \
                                                                               \
    if (new_list1 == EMPTY)                                                    \
      {                                                                        \
        return new_list2;                                                      \
      }                                                                        \
                                                                               \
    else                                                                       \
      {                                                                        \
        TYPE##_list_t *prev = new_list1;                                       \
        TYPE##_list_t *current = new_list1;                                    \
                                                                               \
        while (current != EMPTY)                                               \
          {                                                                    \
            prev = current;                                                    \
            current = current->tail;                                           \
          }                                                                    \
                                                                               \
        prev->tail = new_list2;                                                \
                                                                               \
        return new_list1;                                                      \
      }                                                                        \
  }



/*******************************************************************************
 * function:    Range
 * signature:   Num × Num × Num → T_list*
 * persistence: True
 * performance: O(n)
 * description: Creates a new list that has numerical values in the range
 *              start to end, with spacing given by step. Although this
 *              implementation is polymorphic for numeric types, it will not
 *              work on types that the built-in arithmetic operators cannot
 *              handle.
 ******************************************************************************/
#define DEF_LIST_RANGE(TYPE)                                                   \
  TYPE##_list_t *                                                              \
  TYPE##_list_range (TYPE start, TYPE end, TYPE step)                          \
  {                                                                            \
    TYPE##_list_t *new_list = TYPE##_list_init (start);                        \
    TYPE##_list_t *current = new_list;                                         \
    TYPE i;                                                                    \
    for (i = start + step; i <= end; i += step)                                \
      {                                                                        \
        current->tail = TYPE##_list_init (i);                                  \
        current = current->tail;                                               \
      }                                                                        \
    return new_list;                                                           \
  }



/*******************************************************************************
 * function:    Print List
 * signature:   T_list* → Unit
 * persistence: True
 * performance: O(n)
 * description: Prints the elements of the list to stdout. This function is
 *              polymorphic for any types that have a printf format string.
 ******************************************************************************/
#define DEF_LIST_PRINT(TYPE, FMT)                                              \
  void                                                                         \
  TYPE##_list_print (TYPE##_list_t * list)                                     \
  {                                                                            \
    TYPE##_list_t *current = list;                                             \
    if (current == EMPTY)                                                      \
      {                                                                        \
        printf ("[ ]\n");                                                      \
      }                                                                        \
    else                                                                       \
      {                                                                        \
        printf ("[");                                                          \
        while (current)                                                        \
          {                                                                    \
            printf (FMT", ", current->head);                                   \
            current = current->tail;                                           \
          }                                                                    \
        printf ("\b\b]\n");                                                    \
      }                                                                        \
  }




/*******************************************************************************
 * Batch function definition macros
 ******************************************************************************/
#define DEF_LIST_BASE(TYPE)                                                    \
  DEF_LIST_TYPE(TYPE);                                                         \
  DEF_LIST_LENGTH(TYPE);                                                       \
  DEF_LIST_FIND(TYPE);                                                         \
  DEF_LIST_COUNT(TYPE);                                                        \
  DEF_LIST_DISPOSE(TYPE);                                                      \
  DEF_LIST_INIT(TYPE);                                                         \
  DEF_LIST_APP(TYPE);                                                          \
  DEF_LIST_CONS(TYPE);                                                         \
  DEF_LIST_COPY(TYPE);                                                         \
  DEF_LIST_INSERT(TYPE);                                                       \
  DEF_LIST_INSERTAT(TYPE);                                                     \
  DEF_LIST_DELETE(TYPE);                                                       \
  DEF_LIST_DELETEAT(TYPE);                                                     \
  DEF_LIST_ITER(TYPE);                                                         \
  DEF_LIST_MAP(TYPE, TYPE);                                                    \
  DEF_LIST_REVERSE(TYPE);                                                      \
  DEF_LIST_FILTER(TYPE);                                                       \
  DEF_LIST_APPEND(TYPE);                                                       \
  


#define DEF_LIST_FULL(TYPE, FMT)                                               \
  DEF_LIST_BASE(TYPE);                                                         \
  DEF_LIST_RANGE(TYPE);                                                        \
  DEF_LIST_PRINT(TYPE, FMT);                                                   \



#endif
