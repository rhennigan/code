// quickselect.c
// Copyright (C) 2014 Richard Hennigan

#define SWAP(TYPE, a, b) {						       \
    register TYPE t = (a);						       \
    (a) = (b);								       \
    (b) = t;								       \
  }

#define _DEF_QS(TYPE)							       \
  TYPE qs_##TYPE(TYPE * data, int k) {					       \
    int lo, hi;								       \
    int me;								       \
    int mi, ll, hh;							       \
									       \
    lo = 0;								       \
    hi = k - 1;								       \
    me = (lo + hi) / 2;							       \
									       \
    while (1) {								       \
      if (hi <= lo) return data[me];					       \
      if (hi == lo + 1) {						       \
	if (data[lo] > data[hi]) SWAP(TYPE, data[lo], data[hi]);	       \
	return data[me];						       \
      }									       \
									       \
      mi = (lo + hi) / 2;						       \
      if (data[mi] > data[hi]) SWAP(TYPE, data[mi], data[hi]);		       \
      if (data[lo] > data[hi]) SWAP(TYPE, data[lo], data[hi]);		       \
      if (data[mi] > data[lo]) SWAP(TYPE, data[mi], data[lo]);		       \
									       \
      SWAP(TYPE, data[mi], data[lo + 1]);				       \
									       \
      ll = lo + 1;							       \
      hh = hi;								       \
      while (1) {							       \
	do ll++; while (data[lo] > data[ll]);				       \
	do hh--; while (data[hh] > data[lo]);				       \
	if (hh < ll) break;						       \
	SWAP(TYPE, data[ll], data[hh]);					       \
      }									       \
									       \
      SWAP(TYPE, data[lo], data[hh]);					       \
									       \
      if (hh <= me) lo = ll;						       \
      if (hh >= me) hi = hh - 1;					       \
    }									       \
  }

#define _DEF_MEDIAN(TYPE)						       \
  TYPE median_##TYPE(TYPE * data, int len) {				       \
    TYPE cpy[sizeof(TYPE) * len];					       \
    int i;								       \
    for (i = 0; i < len; i++) {						       \
      cpy[i] = data[i];							       \
    }									       \
    return qs_##TYPE(cpy, len);						       \
  }

_DEF_QS(double);
_DEF_MEDIAN(double);

double median(double * data, int len) {
  return median_double(data, len);
}

double quickselect(double * data, int k) {
  return qs_double(data, k);
}

#undef SWAP
#undef _DEF_QS
#undef _DEF_MEDIAN
