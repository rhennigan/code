#ifndef _LIB_DATA_TUPLE_H
#define _LIB_DATA_TUPLE_H

#define def_tuple(T1, T2)						       \
  typedef struct T1##_##T2##_tuple_s {					       \
    T1 fst;								       \
    T2 snd;								       \
  } T1##_##T2##_tuple_t;



#define def_h_tuple(TYPE)						       \
  typedef struct TYPE##__tuple_s {					       \
    TYPE fst;								       \
    TYPE snd;								       \
  } TYPE##_tuple_t;

#endif
