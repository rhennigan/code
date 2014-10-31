/*
 ********************************************************************************
 * linked_list.h
 * Richard Hennigan
 ********************************************************************************
 */

#ifndef _LINKED_LIST_H
#define _LINKED_LIST_H

#include "../bool.h"
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

#ifndef EMPTY
#define EMPTY NULL
#endif



#define def_list_t(TYPE)                        \
  typedef struct TYPE##_list_s                  \
  {                                             \
   TYPE head;                                   \
   struct TYPE##_list_s *tail;                  \
   } TYPE##_list_t;





#define def_list_length(TYPE)                   \
  int                                           \
  TYPE##_list_length (TYPE##_list_t * list)     \
  {                                             \
    int len = 0;                                \
    TYPE##_list_t *current = list;              \
                                                \
    while (current)                             \
    {                                           \
      len += 1;                                 \
      current = current->tail;                  \
    }                                           \
                                                \
    return len;                                 \
  }





#define def_list_dispose(TYPE)                  \
  void                                          \
  TYPE##_list_dispose (TYPE##_list_t * list)    \
  {                                             \
    TYPE##_list_t *current = list;              \
    TYPE##_list_t *next = list;                 \
    while (current)                             \
    {                                           \
      next = current->tail;                     \
      free (current);                           \
      current = next;                           \
    }                                           \
  }





#define def_list_init(TYPE)                                             \
  TYPE##_list_t *                                                       \
  TYPE##_list_init (TYPE data)                                          \
  {                                                                     \
    TYPE##_list_t *new_list = (TYPE##_list_t *) malloc (sizeof (TYPE##_list_t)); \
    assert (new_list);                                                  \
    new_list->head = data;                                              \
    new_list->tail = EMPTY;                                             \
    return new_list;                                                    \
  }





#define def_list_app(TYPE)                              \
  TYPE##_list_t *                                       \
  TYPE##_list_app (TYPE##_list_t * list, TYPE head)     \
  {                                                     \
    TYPE##_list_t *new_node = TYPE##_list_init (head);  \
    TYPE##_list_t *current = list;                      \
    TYPE##_list_t *prev = list;                         \
    while (current)                                     \
    {                                                   \
      prev = current;                                   \
      current = current->tail;                          \
    }                                                   \
    prev->tail = new_node;                              \
    return list;                                        \
  }





#define def_list_cons(TYPE)                                             \
  TYPE##_list_t *                                                       \
  TYPE##_list_cons (TYPE##_list_t * list, TYPE head)                    \
  {                                                                     \
    TYPE##_list_t *new_list = (TYPE##_list_t *) malloc (sizeof (TYPE##_list_t)); \
    assert (new_list);                                                  \
    new_list->head = head;                                              \
    new_list->tail = list;                                              \
    return new_list;                                                    \
  }





#define def_list_copy(TYPE)                                     \
  TYPE##_list_t *                                               \
  TYPE##_list_copy (TYPE##_list_t * list)                       \
  {                                                             \
    if (list == EMPTY)                                          \
    {                                                           \
      return EMPTY;                                             \
    }                                                           \
    else                                                        \
    {                                                           \
      TYPE##_list_t *current = list->tail;                      \
      TYPE##_list_t *new_list = TYPE##_list_init (list->head);  \
      TYPE##_list_t *new_current = new_list;                    \
      while (current)                                           \
      {                                                         \
        new_current->tail = TYPE##_list_init (current->head);   \
        current = current->tail;                                \
        new_current = new_current->tail;                        \
      }                                                         \
      return new_list;                                          \
    }                                                           \
  }





#define def_list_find(TYPE)                                             \
  bool                                                                  \
  TYPE##_list_find (TYPE##_list_t * list, TYPE data, bool (*cmp)(TYPE, TYPE)) \
  {                                                                     \
    TYPE##_list_t *current = list;                                      \
                                                                        \
    while (current)                                                     \
    {                                                                   \
      if ((*cmp)(current->head, data))                                  \
      {                                                                 \
        return true;                                                    \
      }                                                                 \
      current = current->tail;                                          \
    }                                                                   \
                                                                        \
    return false;                                                       \
  }





#define def_list_count(TYPE)                                            \
  int                                                                   \
  TYPE##_list_count (TYPE##_list_t * list, TYPE data, bool (*cmp)(TYPE, TYPE)) \
  {                                                                     \
    int count = 0;                                                      \
    TYPE##_list_t *current = list;                                      \
                                                                        \
    while (current)                                                     \
    {                                                                   \
      count = (*cmp)(current->head, data) ? count + 1 : count;          \
      current = current->tail;                                          \
    }                                                                   \
                                                                        \
    return count;                                                       \
  }





#define def_list_reverse(TYPE)                                          \
  TYPE##_list_t *                                                       \
  TYPE##_list_reverse (TYPE##_list_t * list)                            \
  {                                                                     \
    TYPE##_list_t *reversed_list = EMPTY;                               \
    TYPE##_list_t *current = list;                                      \
                                                                        \
    while (current)                                                     \
    {                                                                   \
      reversed_list = TYPE##_list_cons (reversed_list, current->head);  \
      current = current->tail;                                          \
    }                                                                   \
                                                                        \
    return reversed_list;                                               \
  }





#define def_list_insert(TYPE)                           \
  TYPE##_list_t *                                       \
  TYPE##_list_insert (TYPE##_list_t * list, TYPE data)  \
  {                                                     \
    TYPE##_list_t *new_list = TYPE##_list_copy (list);  \
    new_list = TYPE##_list_cons (new_list, data);       \
    return new_list;                                    \
  }





#define def_list_insertat(TYPE)                                         \
  TYPE##_list_t *                                                       \
  TYPE##_list_insertat (TYPE##_list_t * list, TYPE data, int position)  \
  {                                                                     \
    assert (position >= 0);                                             \
    if (position == 0)                                                  \
    {                                                                   \
      return TYPE##_list_insert (list, data);                           \
    }                                                                   \
    else                                                                \
    {                                                                   \
      TYPE##_list_t *new_list = TYPE##_list_copy (list);                \
      TYPE##_list_t *node = TYPE##_list_init (data);                    \
      TYPE##_list_t *current = new_list;                                \
      TYPE##_list_t *prev = new_list;                                   \
      int i;                                                            \
      for (i = position; i > 0 && current; i--)                         \
      {                                                                 \
        prev = current;                                                 \
        current = current->tail;                                        \
      }                                                                 \
      assert (i < 1);                                                   \
      prev->tail = node;                                                \
      node->tail = current;                                             \
      return new_list;                                                  \
    }                                                                   \
  }





#define def_list_remove(TYPE)                                   \
  TYPE##_list_t *                                               \
  TYPE##_list_remove (TYPE##_list_t * list, int position)       \
  {                                                             \
    assert (position >= 0);                                     \
                                                                \
    TYPE##_list_t *new_list = TYPE##_list_copy (list);          \
    TYPE##_list_t *junk = EMPTY;                                \
                                                                \
    if (position == 0)                                          \
    {                                                           \
      junk = new_list;                                          \
      new_list = new_list->tail;                                \
      free (junk);                                              \
      return new_list;                                          \
    }                                                           \
                                                                \
    else                                                        \
    {                                                           \
      TYPE##_list_t *current = new_list;                        \
                                                                \
      int i;                                                    \
      for (i = position; i > 1 && current; i--)                 \
      {                                                         \
        current = current->tail;                                \
      }                                                         \
      assert (current);                                         \
      junk = current->tail;                                     \
      assert (junk);                                            \
      current->tail = junk->tail;                               \
      free (junk);                                              \
      return new_list;                                          \
    }                                                           \
  }





#define def_list_append(TYPE)                                           \
  TYPE##_list_t *                                                       \
  TYPE##_list_append (TYPE##_list_t * list1, TYPE##_list_t * list2)     \
  {                                                                     \
    TYPE##_list_t *new_list1 = TYPE##_list_copy (list1);                \
    TYPE##_list_t *new_list2 = TYPE##_list_copy (list2);                \
                                                                        \
    if (!new_list1)                                                     \
    {                                                                   \
      return new_list2;                                                 \
    }                                                                   \
    else                                                                \
    {                                                                   \
      TYPE##_list_t *prev = new_list1;                                  \
      TYPE##_list_t *current = new_list1;                               \
                                                                        \
      while (current)                                                   \
      {                                                                 \
        prev = current;                                                 \
        current = current->tail;                                        \
      }                                                                 \
                                                                        \
      prev->tail = new_list2;                                           \
                                                                        \
      return new_list1;                                                 \
    }                                                                   \
  }





#define def_list_range(TYPE)                            \
  TYPE##_list_t *                                       \
  TYPE##_list_range (TYPE start, TYPE end, TYPE step)   \
  {                                                     \
    TYPE##_list_t *new_list = TYPE##_list_init (start); \
    TYPE##_list_t *current = new_list;                  \
    TYPE i;                                             \
    for (i = start + step; i <= end; i += step)         \
    {                                                   \
      current->tail = TYPE##_list_init (i);             \
      current = current->tail;                          \
    }                                                   \
    return new_list;                                    \
  }





#define def_list_print(TYPE, FMT)               \
  void                                          \
  TYPE##_list_print (TYPE##_list_t * list)      \
  {                                             \
    TYPE##_list_t *current = list;              \
    if (!current)                               \
    {                                           \
      printf ("[ ]\n");                         \
    }                                           \
    else                                        \
    {                                           \
      printf ("[");                             \
      while (current)                           \
      {                                         \
        printf (FMT", ", current->head);        \
        current = current->tail;                \
      }                                         \
      printf ("\b\b]\n");                       \
    }                                           \
  }





#define def_list_base(TYPE)                     \
  def_list_t(TYPE);                             \
  def_list_length(TYPE);                        \
  def_list_dispose(TYPE);                       \
  def_list_init(TYPE);                          \
  def_list_app(TYPE);                           \
  def_list_cons(TYPE);                          \
  def_list_copy(TYPE);                          \
  def_list_find(TYPE);                          \
  def_list_count(TYPE);                         \
  def_list_reverse(TYPE);                       \
  def_list_insert(TYPE);                        \
  def_list_insertat(TYPE);                      \
  def_list_remove(TYPE);                        \
  def_list_append(TYPE);





#define def_list_full(TYPE, FMT)                \
  def_list_base(TYPE);                          \
  def_list_range(TYPE);                         \
  def_list_print(TYPE, FMT);






#endif
