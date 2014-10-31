/*
 ********************************************************************************
 * circular_linked_list.h
 * Richard Hennigan
 ********************************************************************************
 */

#ifndef _CIRCULAR_LINKED_LIST_H
#define _CIRCULAR_LINKED_LIST_H

#include "../bool.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#ifndef EMPTY
#define EMPTY NULL
#endif



#define def_clist_t(TYPE)                                                       \
  typedef struct TYPE##_clist_s                                                 \
  {                                                                             \
    struct TYPE##_clist_s *prev;                                                \
    TYPE data;                                                                  \
    struct TYPE##_clist_s *next;                                                \
  } TYPE##_clist_t;



/********************************************************************************
 * function:    Length
 * signature:   T_clist_t* → Int
 * persistence: True
 * performance: O(n)
 * description: Returns the number of items in the list
 *******************************************************************************/
#define def_clist_length(TYPE)                                                  \
  int                                                                           \
  TYPE##_clist_length (TYPE##_clist_t * list)                                   \
  {                                                                             \
    int len = 0;                                                                \
    TYPE##_clist_t *start = list;                                               \
    TYPE##_clist_t *current = list->next;                                       \
                                                                                \
    while (current != start)                                                    \
      {                                                                         \
        len += 1;                                                               \
        current = current->next;                                                \
      }                                                                         \
                                                                                \
    return len;                                                                 \
  }                                                                             \



/********************************************************************************
 * function:    Find
 * signature:   T_clist* × T × (T × T → Bool) → Bool
 * persistence: True
 * performance: O(n)
 * description: Returns true if obj is present in the list and false otherwise.
 *******************************************************************************/
#define def_clist_find(TYPE)                                                    \
  bool                                                                          \
  TYPE##_clist_find (TYPE##_clist_t * list, TYPE obj, bool (*cmp)(TYPE, TYPE))  \
  {                                                                             \
    TYPE##_clist_t *start = list;                                               \
    TYPE##_clist_t *current = list;                                             \
                                                                                \
    do                                                                          \
      {                                                                         \
        if ((*cmp)(current->data, obj))                                         \
          {                                                                     \
            return true;                                                        \
          }                                                                     \
                                                                                \
        current = current->next;                                                \
                                                                                \
      }                                                                         \
    while (current != start);                                                   \
                                                                                \
    return false;                                                               \
  }                                                                             \



/********************************************************************************
 * function:    Count
 * signature:   T_clist* × T × (T × T → Bool) → Int
 * persistence: True
 * performance: O(n)
 * description: Returns the number of times that obj appears in the list.
 *******************************************************************************/
#define def_clist_count(TYPE)                                                   \
  int                                                                           \
  TYPE##_clist_count (TYPE##_clist_t * list, TYPE obj, bool (*cmp)(TYPE, TYPE)) \
  {                                                                             \
    int count = 0;                                                              \
    TYPE##_clist_t *start = list;                                               \
    TYPE##_clist_t *current = list;                                             \
                                                                                \
    do                                                                          \
      {                                                                         \
        if ((*cmp)(current->data, obj))                                         \
          {                                                                     \
            count += 1;                                                         \
          }                                                                     \
                                                                                \
        current = current->next;                                                \
                                                                                \
      }                                                                         \
    while (current != start);                                                   \
                                                                                \
    return count;                                                               \
  }                                                                             \



/********************************************************************************
 * function:    Dispose List
 * signature:   T_clist* → Unit
 * persistence: False
 * performance: O(n)
 * description: Releases the memory that was allocated for the list.
 *******************************************************************************/
#define def_clist_dispose(TYPE)                                                 \
  void                                                                          \
  TYPE##_clist_dispose (TYPE##_clist_t * list)                                  \
  {                                                                             \
    TYPE##_clist_t *current = list;                                             \
    TYPE##_clist_t *next = list->next;                                          \
    int len = TYPE##_clist_length (list);                                       \
    int i;                                                                      \
                                                                                \
    for (i = 0; i < len + 1; i++)                                               \
      {                                                                         \
        next = current->next;                                                   \
        free (current);                                                         \
        current = next;                                                         \
      }                                                                         \
  }                                                                             \



/********************************************************************************
 * function:    Initialize List
 * signature:   T → T_clist*
 * persistence: True
 * performance: O(1)
 * description: Creates a circular list with a single element.
 *******************************************************************************/
#define def_clist_init(TYPE)                                                    \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_init (TYPE data)                                                 \
  {                                                                             \
    TYPE##_clist_t *list = (TYPE##_clist_t *) malloc (sizeof (TYPE##_clist_t)); \
    assert (list);                                                              \
    list->prev = list;                                                          \
    list->data = data;                                                          \
    list->next = list;                                                          \
    return list;                                                                \
  }                                                                             \



/********************************************************************************
 * function:    Add to End
 * signature:   T_clist* × T → T_clist*
 * persistence: False
 * performance: O(1)
 * description: Adds a single element to the end of the list.
 *******************************************************************************/
#define def_clist_app(TYPE)                                                     \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_app (TYPE##_clist_t * list, TYPE data)                           \
  {                                                                             \
    TYPE##_clist_t *prev = list->prev;                                          \
    TYPE##_clist_t *next = list;                                                \
    TYPE##_clist_t *new_list = TYPE##_clist_init (data);                        \
                                                                                \
    prev->next = new_list;                                                      \
    next->prev = new_list;                                                      \
                                                                                \
    new_list->prev = prev;                                                      \
    new_list->next = next;                                                      \
                                                                                \
    return list;                                                                \
  }                                                                             \



/********************************************************************************
 * function:    Add to Beginning
 * signature:   T_clist* × T → T_clist*
 * persistence: False
 * performance: O(1)
 * description: Adds a single element to the beginning of the list.
 *******************************************************************************/
#define def_clist_cons(TYPE)                                                    \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_cons (TYPE##_clist_t * list, TYPE data)                          \
  {                                                                             \
    TYPE##_clist_t *prev = list->prev;                                          \
    TYPE##_clist_t *next = list;                                                \
    TYPE##_clist_t *new_list = TYPE##_clist_init (data);                        \
                                                                                \
    prev->next = new_list;                                                      \
    next->prev = new_list;                                                      \
                                                                                \
    new_list->prev = prev;                                                      \
    new_list->next = next;                                                      \
                                                                                \
    return new_list;                                                            \
  }                                                                             \



/********************************************************************************
 * function:    Copy
 * signature:   T_clist* → T_clist*
 * persistence: True
 * performance: O(n)
 * description: Returns a copy of the input list, leaving the original unchanged.
 *******************************************************************************/
#define def_clist_copy(TYPE)                                                    \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_copy (TYPE##_clist_t * list)                                     \
  {                                                                             \
    TYPE##_clist_t *last = list->prev;                                          \
    TYPE##_clist_t *current = list->next;                                       \
    TYPE##_clist_t *new_list = TYPE##_clist_init (list->data);                  \
                                                                                \
    while (current != last)                                                     \
      {                                                                         \
        new_list = TYPE##_clist_app (new_list, current->data);                  \
        current = current->next;                                                \
      }                                                                         \
    new_list = TYPE##_clist_app (new_list, current->data);                      \
                                                                                \
    return new_list;                                                            \
  }                                                                             \



/********************************************************************************
 * function:    Add to Beginning
 * signature:   T_clist* × T → T_clist*
 * persistence: True
 * performance: O(n)
 * description: Adds a single element to the beginning of a copy of the list.
 *              The input list is unchanged.
 *******************************************************************************/
#define def_clist_insert(TYPE)                                                  \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_insert (TYPE##_clist_t * list, TYPE data)                        \
  {                                                                             \
    TYPE##_clist_t *new_list = TYPE##_clist_copy (list);                        \
    TYPE##_clist_t *new_node = TYPE##_clist_init (data);                        \
    new_list->prev->next = new_node;                                            \
    new_list->prev = new_node;                                                  \
    new_node->prev = new_list->prev;                                            \
    new_node->next = new_list;                                                  \
    return new_node;                                                            \
  }                                                                             \



/********************************************************************************
 * function:    Add at Location
 * signature:   T_clist* × T × Int → T_clist*
 * persistence: True
 * performance: O(n)
 * description: Adds a single element at an indexed location of a copy of the
 *              list. The input list is unchanged.
 *******************************************************************************/
#define def_clist_insertat(TYPE)                                                \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_insertat (TYPE##_clist_t * list, TYPE data, int position)        \
  {                                                                             \
    assert (position > -1);                                                     \
    TYPE##_clist_t *finish = list;                                              \
    TYPE##_clist_t *current = list;                                             \
    TYPE##_clist_t *new_list_current;                                           \
    TYPE##_clist_t *new_list_start;                                             \
                                                                                \
    if (position == 0)                                                          \
      {                                                                         \
        new_list_current = TYPE##_clist_init (data);                            \
      }                                                                         \
    else                                                                        \
      {                                                                         \
        new_list_current = TYPE##_clist_init (current->data);                   \
        current = current->next;                                                \
      }                                                                         \
                                                                                \
    new_list_start = new_list_current;                                          \
    position--;                                                                 \
                                                                                \
    do                                                                          \
      {                                                                         \
        if (position == 0)                                                      \
          {                                                                     \
            new_list_current = TYPE##_clist_app (new_list_current, data);       \
          }                                                                     \
        new_list_current = TYPE##_clist_app (new_list_current, current->data);  \
        current = current->next;                                                \
        position--;                                                             \
      }                                                                         \
    while (current != finish);                                                  \
                                                                                \
    if (position == 0)                                                          \
      {                                                                         \
        new_list_current = TYPE##_clist_app (new_list_current, data);           \
      }                                                                         \
                                                                                \
    assert (position < 1);                                                      \
    return new_list_start;                                                      \
  }



/********************************************************************************
 * function:    Delete
 * signature:   T_clist* → T_clist*
 * persistence: True
 * performance: O(n)
 * description: Returns a copy of the input list with the first element removed.
 *              The input list is unchanged.
 *******************************************************************************/
#define def_clist_delete(TYPE)                                                  \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_delete (TYPE##_clist_t * list)                                   \
  {                                                                             \
    TYPE##_clist_t *new_list = TYPE##_clist_copy (list);                        \
    TYPE##_clist_t *prev = new_list->prev;                                      \
    TYPE##_clist_t *next = new_list->next;                                      \
                                                                                \
    free (new_list);                                                            \
                                                                                \
    prev->next = next;                                                          \
    next->prev = prev;                                                          \
                                                                                \
    return next;                                                                \
  }                                                                             \



/********************************************************************************
 * function:    Filter
 * signature:   T_clist* × T × (T × T → Bool) → T_clist*
 * persistence: True
 * performance: O(n)
 * description: Returns a copy of the input list with all instances of obj
 *              deleted. The input list is unchanged. (*cmp) is a pointer to a
 *              function that determines when two objects of type T are equal.
 *******************************************************************************/
#define def_clist_filter(TYPE)                                                  \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_filter (TYPE##_clist_t *list, TYPE obj, bool (*cmp)(TYPE, TYPE)) \
  {                                                                             \
    TYPE##_clist_t *new_list = TYPE##_clist_copy (list);                        \
    TYPE##_clist_t *start = new_list;                                           \
    TYPE##_clist_t *prev = new_list->prev;                                      \
    TYPE##_clist_t *next = new_list->next;                                      \
                                                                                \
    while ((*cmp)(start->data, obj))                                            \
      {                                                                         \
        prev->next = next;                                                      \
        next->prev = prev;                                                      \
        start = start->next;                                                    \
        free (new_list);                                                        \
        new_list = start;                                                       \
        next = next->next;                                                      \
      }                                                                         \
                                                                                \
    TYPE##_clist_t *current = new_list;                                         \
                                                                                \
    do                                                                          \
      {                                                                         \
        if ((*cmp)(current->data, obj))                                         \
          {                                                                     \
            prev->next = next;                                                  \
            next->prev = prev;                                                  \
            free (current);                                                     \
            current = next;                                                     \
            next = next->next;                                                  \
          }                                                                     \
                                                                                \
        else                                                                    \
          {                                                                     \
            prev = prev->next;                                                  \
            current = current->next;                                            \
            next = next->next;                                                  \
          }                                                                     \
                                                                                \
      }                                                                         \
    while (current != start);                                                   \
                                                                                \
    return new_list;                                                            \
  }                                                                             \



/********************************************************************************
 * function:    Iterate
 * signature:   T_clist* × (T → Unit) → Unit
 * persistence: True
 * performance: O(n)
 * description: Applies the given function to each element of the list.
 *******************************************************************************/
#define def_clist_iter(TYPE)                                                    \
  void                                                                          \
  TYPE##_clist_iter (TYPE##_clist_t * list, void (*f)(TYPE))                    \
  {                                                                             \
    if (list == EMPTY)                                                          \
      {                                                                         \
        return;                                                                 \
      }                                                                         \
                                                                                \
    else                                                                        \
      {                                                                         \
        TYPE##_clist_t * start = list;                                          \
        TYPE##_clist_t * current = list;                                        \
                                                                                \
        do                                                                      \
          {                                                                     \
            (*f)(current->data);                                                \
            current = current->next;                                            \
          }                                                                     \
        while (current != start);                                               \
                                                                                \
        return;                                                                 \
      }                                                                         \
  }



/********************************************************************************
 * function:    Map
 * signature:   T1_clist* × (T1 → T2) → T2_clist*
 * persistence: True
 * performance: O(n)
 * description: Applies the given function to each element of the list and
 *              returns the list of results.
 *******************************************************************************/
#define def_clist_map(T1, T2)                                                   \
  T2##_clist_t *                                                                \
  T1##_##T2##_clist_map (T1##_clist_t * list, T2 (*f)(T1))                      \
  {                                                                             \
    if (list == EMPTY)                                                          \
      {                                                                         \
        return EMPTY;                                                           \
      }                                                                         \
                                                                                \
    else                                                                        \
      {                                                                         \
        T1##_clist_t * start = list;                                            \
        T1##_clist_t * current = list;                                          \
        T2##_clist_t * new_list = T2##_clist_init((*f)(current->data));         \
        current = current->next;                                                \
                                                                                \
        while (current != start)                                                \
          {                                                                     \
            new_list = T2##_clist_app(new_list, (*f)(current->data));           \
            current = current->next;                                            \
          }                                                                     \
                                                                                \
        return new_list;                                                        \
      }                                                                         \
  }



/********************************************************************************
 * function:    Append
 * signature:   T_clist* × T_clist* → T_clist*
 * persistence: True
 * performance: O(n)
 * description: Joins two circular lists into one, where the first element is
 *              the first element of list1, and the last element is the last
 *              element of list2.  The input lists are unchanged.
 *******************************************************************************/
#define def_clist_append(TYPE)                                                  \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_append (TYPE##_clist_t * list1, TYPE##_clist_t * list2)          \
  {                                                                             \
    TYPE##_clist_t *left = TYPE##_clist_copy (list1);                           \
    TYPE##_clist_t *right = TYPE##_clist_copy (list2);                          \
                                                                                \
    left->prev->next = right;                                                   \
    right->prev->next = left;                                                   \
    left->prev = right->prev;                                                   \
    right->prev = left->prev;                                                   \
                                                                                \
    return left;                                                                \
  }                                                                             \



/********************************************************************************
 * function:    Range
 * signature:   Int × Int × Int → T_clist*
 * persistence: True
 * performance: O(n)
 * description: Creates a new list that has numerical values in the range
 *              start to end, with spacing given by step. Although this
 *              implementation is polymorphic for numeric types, it will not
 *              work on types that the built-in arithmetic operators cannot
 *              handle.
 *******************************************************************************/
#define def_clist_range(TYPE)                                                   \
  TYPE##_clist_t *                                                              \
  TYPE##_clist_range (TYPE start, TYPE end, TYPE step)                          \
  {                                                                             \
    TYPE##_clist_t *list = TYPE##_clist_init (start);                           \
    TYPE i;                                                                     \
    for (i = start + step; i <= end; i += step)                                 \
      {                                                                         \
        list = TYPE##_clist_app (list, i);                                      \
      }                                                                         \
    return list;                                                                \
  }                                                                             \



/********************************************************************************
 * function:    Print List
 * signature:   T_clist* → Unit
 * persistence: True
 * performance: O(n)
 * description: Prints the elements of the list to stdout. This function is
 *              polymorphic for any types that have a printf format string.
 *******************************************************************************/
#define def_clist_print(TYPE, FMT)                                              \
  void                                                                          \
  TYPE##_clist_print (TYPE##_clist_t * list)                                    \
  {                                                                             \
    if (list == EMPTY)                                                          \
      {                                                                         \
        printf ("[ ]\n");                                                       \
      }                                                                         \
                                                                                \
    else                                                                        \
      {                                                                         \
        printf ("[");                                                           \
                                                                                \
        TYPE##_clist_t *last = list->prev;                                      \
        TYPE##_clist_t *current = list;                                         \
                                                                                \
        while (current != last)                                                 \
          {                                                                     \
            printf (FMT", ", current->data);                                    \
            current = current->next;                                            \
          }                                                                     \
                                                                                \
        printf (FMT"]\n", current->data);                                       \
      }                                                                         \
  }                                                                             \



/********************************************************************************
 * Batch function definition macros
 *******************************************************************************/
#define def_clist_base(TYPE)                                                    \
  def_clist_t(TYPE);                                                            \
  def_clist_length(TYPE);                                                       \
  def_clist_find(TYPE);                                                         \
  def_clist_count(TYPE);                                                        \
  def_clist_dispose(TYPE);                                                      \
  def_clist_init(TYPE);                                                         \
  def_clist_app(TYPE);                                                          \
  def_clist_cons(TYPE);                                                         \
  def_clist_copy(TYPE);                                                         \
  def_clist_insert(TYPE);                                                       \
  def_clist_insertat(TYPE);                                                     \
  def_clist_delete(TYPE);                                                       \
  def_clist_filter(TYPE);                                                       \
  def_clist_iter(TYPE);                                                         \
  def_clist_append(TYPE);                                                       \
  


#define def_clist_full(TYPE, FMT)                                               \
  def_clist_base(TYPE);                                                         \
  def_clist_range(TYPE);                                                        \
  def_clist_print(TYPE, FMT);                                                   \



#endif
