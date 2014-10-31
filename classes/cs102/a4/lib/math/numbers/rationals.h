#ifndef _LIB_MATH_NUMBERS_RATIONALS_H
#define _LIB_MATH_NUMBERS_RATIONALS_H

#include <stdlib.h>
#include <stdio.h>

typedef struct rational_s {
  int num;
  int den;
} rational_t;

char * q_to_string(rational_t q) {
  char *str = malloc(BUFSIZ);
  if (q.den == 1) {
    snprintf(str, BUFSIZ, "%d", q.num);
  } else {
    snprintf(str, BUFSIZ, "%d / %d", q.num, q.den);
  }
  return str;
}

int _gcd(int u, int v) {
  return (v != 0) ? _gcd(v, u % v) : u;
}

rational_t q_reduce(rational_t q) {
  int d = _gcd(q.num, q.den);
  rational_t _q = (rational_t){ q.num / d, q.den / d };
  return (_q.den >= 0 ? _q : (rational_t) {-_q.num, -_q.den});
}

rational_t q_add(rational_t a, rational_t b) {
  rational_t _a = {  a.num *  b.den,  a.den * b.den };
  rational_t _b = {  b.num *  a.den,  b.den * a.den };
  rational_t  q = { _a.num + _b.num, _a.den         };
  return q_reduce(q);
}

rational_t q_mult(rational_t a, rational_t b) {
  rational_t q = { a.num * b.num, a.den * b.den };
  return q_reduce(q);
}

rational_t q_neg(rational_t a) {
  rational_t q = { -a.num, a.den };
  return q_reduce(q);
}

rational_t q_sub(rational_t a, rational_t b) {
  return q_reduce( q_add (a, q_neg (b) ) );
}

rational_t q_div(rational_t a, rational_t b) {
  if (b.num == 0) {
      printf("error: division by zero\n");
      exit(1);
    } else {
      rational_t b_inv = { b.den, b.num };
      return q_reduce( q_mult (a, b_inv));
    }
}

rational_t int_to_q(int x) {
  return ((rational_t){ x, 1 });
}

#endif
