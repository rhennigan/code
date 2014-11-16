// bst.c - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bst.h"

#define MIN(a, b) ((a) < (b) ? (a) : (b))
#define MIN3(a, b, c) MIN(a, MIN(b, c))
#define MAX(a, b) ((a) > (b) ? (a) : (b))
#define MAX3(a, b, c) MAX(a, MAX(b, c))
#define ABS(a) ((a) < 0 ? -(a) : (a))

#define SWAP(a, b) do {                         \
    register void * t = (a);                    \
    (a) = (b);                                  \
    (b) = t;                                    \
  } while (0);

/******************************************************************************/
/* UNICODE CHARACTERS FOR TREE DRAWING                                        */
/******************************************************************************/

#define B_HR "\u2500"  // horizontal bar
#define B_TL "\u250C"  // top-left box corner
#define B_TR "\u2510"  // top-right box corner
#define B_BL "\u2514"  // bottom-left box corner
#define B_BR "\u2518"  // bottom-right box corner
#define B_VT "\u2502"  // vertical bar

/******************************************************************************/
/* PROTECTED MEMBER ACCESS FUNCTIONS                                          */
/******************************************************************************/

static inline void check_null(void * addr, const char * msg) {
  if (addr == NULL) {
    printf("%p: %s\n", addr, msg);
    exit(EXIT_FAILURE);
  }
}

// Member read functions

static inline bst_t * get_left(bst_t * bst) {
  check_null(bst, "get_left");
  return bst->left;
}

static inline bst_t * get_parent(bst_t * bst) {
  check_null(bst, "get_parent");
  return bst->parent;
}

static inline bst_t * get_right(bst_t * bst) {
  check_null(bst, "get_right");
  return bst->right;
}

static inline void * get_data(bst_t * bst) {
  check_null(bst, "get_data");
  return bst->data;
}

static inline size_t get_depth(bst_t * bst) {
  check_null(bst, "get_depth");
  return bst->depth;
}

// Member write functions

static inline void set_left(bst_t * bst, bst_t * new) {
  check_null(bst, "set_left");
  bst->left = new;
}

static inline void set_parent(bst_t * bst, bst_t * new) {
  check_null(bst, "set_parent");
  bst->parent = new;
}

static inline void set_right(bst_t * bst, bst_t * new) {
  check_null(bst, "set_right");
  bst->right = new;
}

static inline void set_data(bst_t * bst, void * data) {
  check_null(bst, "set_data");
  bst->data = data;
}

static inline void set_depth(bst_t * bst, size_t depth) {
  check_null(bst, "set_depth");
  bst->depth = depth;
}

// Member query functions

static inline bool has_left(bst_t * bst) {
  return get_left(bst) != NULL;
}

static inline bool has_parent(bst_t * bst) {
  return get_parent(bst) != NULL;
}

static inline bool has_right(bst_t * bst) {
  return get_right(bst) != NULL;
}

static inline bool has_data(bst_t * bst) {
  return get_data(bst) != NULL;
}

/******************************************************************************/
/* ADDITIONAL PRIVATE FUNCTIONS                                               */
/******************************************************************************/

static inline bool is_leaf(bst_t * bst) {
  return has_data(bst) && !has_left(bst) && !has_right(bst);
}

static bool is_left(bst_t * bst) {
  if (!has_parent(bst)) return false;
  bst_t * p = get_parent(bst);
  return get_left(p) == bst;
}

static bool is_right(bst_t * bst) {
  if (!has_parent(bst)) return false;
  bst_t * p = get_parent(bst);
  return get_right(p) == bst;
}

void bst_update_depth(bst_t * bst) {
  if (has_parent(bst))
    set_depth(bst, get_depth(get_parent(bst)) + 1);
  else
    set_depth(bst, 0);
  if (has_left(bst))
    bst_update_depth(get_left(bst));
  if (has_right(bst))
    bst_update_depth(get_right(bst));
}

bst_t * rotate_right(bst_t * bst) {
  bst_t * p = get_parent(bst);
  bst_t * root = bst;
  bst_t * pivot = get_left(root);
  set_left(root, get_right(pivot));
  if (has_left(root)) set_parent(get_left(root), root);
  set_right(pivot, root);
  set_parent(root, pivot);
  set_parent(pivot, p);
  return pivot;
}

bst_t * rotate_left(bst_t * bst) {
  bst_t * p = get_parent(bst);
  bst_t * root = bst;
  bst_t * pivot = get_right(root);
  set_right(root, get_left(pivot));
  if (has_right(root)) set_parent(get_right(root), root);
  set_left(pivot, root);
  set_parent(root, pivot);
  set_parent(pivot, p);
  return pivot;
}

static void inc_p_path(bst_t ** bst) {
  *bst = bst_balance(*bst);
  if (has_parent(*bst)) {
    bst_t * p = get_parent(*bst);
    inc_p_path(&p);
  }
}

static inline int32_t bal(bst_t * bst) {
  int32_t llc = (int32_t)bst_node_count(get_left(bst));
  int32_t rlc = (int32_t)bst_node_count(get_right(bst));
  return rlc - llc;
}

/******************************************************************************/
/* PUBLIC FUNCTIONS                                                           */
/******************************************************************************/

static bst_t * balance3(bst_t * bst) {
  bst_t * p = get_parent(bst);
  list_t * data = NULL;
  bst_flatten(bst, &data, IN_ORDER);
  /* data = list_reverse(data); */
  bst_dispose(bst);
  void * a = list_head(data);
  void * b = list_head(list_tail(data));
  void * c = list_head(list_tail(list_tail(data)));
  list_dispose(data);
  bst = bst_init();
  set_left(bst, bst_init());
  set_right(bst, bst_init());
  set_data(get_left(bst), c);
  set_data(bst, b);
  set_data(get_right(bst), a);
  set_parent(get_left(bst), bst);
  set_parent(bst, p);
  set_parent(get_right(bst), bst);
  return bst;
}

bst_t * bst_balance(bst_t * bst) {
  /* printf("balancing %p\n", bst); */
  if (bst == NULL || is_leaf(bst)) return bst;
  /* printf("bst_node_count(bst) = %lu\n", bst_node_count(bst)); */
  int b = bal(bst);
  if (bst_node_count(bst) == 3 && b != 0) {
    return balance3(bst);
  }
  if (has_left(bst) && ABS(bal(get_left(bst)))) {
    set_left(bst, bst_balance(get_left(bst)));
  }
  if (has_right(bst) && ABS(bal(get_right(bst)))) {
    set_right(bst, bst_balance(get_right(bst)));
  }
  while (bal(bst) / (int)bst_height(bst) > 0) {
    bst = rotate_left(bst);
  }
  while ((-bal(bst)) / ((int)bst_height(bst)) > 0) {
    bst = rotate_right(bst);
  }
  return bst;
}

size_t bst_leaf_count(bst_t * bst) {
  if (bst == NULL) {
    return 0;
  } else if (is_leaf(bst)) {
    return 1;
  } else {
    return bst_leaf_count(get_left(bst)) + bst_leaf_count(get_right(bst));
  }
}

size_t bst_node_count(bst_t * bst) {
  if (bst == NULL) {
    return 0;
  } else {
    return 1 + bst_node_count(get_left(bst)) + bst_node_count(get_right(bst));
  }
}

size_t bst_height(bst_t * bst) {
  if (bst == NULL) {
    return 0;
  } else if (is_leaf(bst)) {
    return 1;
  } else {
    size_t ld = bst_height(get_left(bst));
    size_t rd = bst_height(get_right(bst));
    size_t d = 1 + MAX(ld, rd);
    return d;
  }
}

void bst_dispose(bst_t * bst) {
  if (bst == NULL) return;
  bst_t ** tmp = &bst;
  bst_dispose(get_left(bst));
  bst_dispose(get_right(bst));
  free(bst);
  *tmp = NULL;
}

void bst_dump(bst_t * bst, order_t order);

void bst_flatten(bst_t * bst, list_t ** list, order_t order) {
  if (bst == NULL) return;
  switch (order) {
    case PRE_ORDER:
      *list = list_cons(*list, get_data(bst));
      bst_flatten(get_left(bst), list, order);
      bst_flatten(get_right(bst), list, order);
      break;
    case IN_ORDER:
      bst_flatten(get_left(bst), list, order);
      *list = list_cons(*list, get_data(bst));
      bst_flatten(get_right(bst), list, order);
      break;
    case POST_ORDER:
      bst_flatten(get_left(bst), list, order);
      bst_flatten(get_right(bst), list, order);
      *list = list_cons(*list, get_data(bst));
      break;
  }  // end switch (order)
}

bst_t * bst_init() {
  bst_t * bst = malloc(sizeof(bst_t));
  check_null(bst, "bst_init: malloc");
  set_left(bst, NULL);
  set_parent(bst, NULL);
  set_right(bst, NULL);
  set_data(bst, NULL);
  set_depth(bst, 0);
  return bst;
}

void bst_insert(bst_t * bst, void * data, cmp_fun cmp) {
  void * td = get_data(bst);
  if (td == NULL) {
    set_data(bst, data);
    return;
  }
  int32_t diff = (*cmp)(data, td);
  if (diff == 0) {
    return;
  } else {  // (diff != 0)
    bool goleft = diff < 0 ? true : false;
    bst_t * next = goleft ? get_left(bst) : get_right(bst);
    if (next == NULL) {
      next = bst_init();  // new pointer, need to update parent
      goleft ? set_left(bst, next) : set_right(bst, next);
      set_parent(next, bst);
      set_data(next, data);
      return;
    } else {  // (next != NULL)
      bst_insert(next, data, cmp);
    }  // end if (next == NULL)
  }  // end if (diff == 0)
}

/* void bst_print(bst_t * bst, pr_fun pf) { */
/*   if (bst == NULL) return; */
/*   bst_print(get_left(bst), pf); */
/*   (*pf)(bst); */
/*   bst_print(get_right(bst), pf); */
/* } */

void bst_remove(bst_t * bst, void * data, cmp_fun cmp);

bool bst_search(bst_t * bst, void * data, cmp_fun cmp) {
  if (cmp(get_data(bst), data) == 0) return true;
}

static inline void show_trunks(trunk_t * p) {
  if (!p) return;
  show_trunks(p->prev);
  printf("%s", p->str);
}

void bst_print(bst_t * bst, trunk_t * prev, pr_fun pf) {
  if (bst == NULL) return;
  trunk_t trunk = { prev, "    " };
  char * prev_str = trunk.str;
  bst_print(get_left(bst), &trunk, pf);

  if (!prev) {
    trunk.str = B_HR""B_HR;
  } else if (is_left(bst)) {
    trunk.str = "\b"B_TL""B_HR""B_HR;
    prev_str = "   "B_VT;
  } else {
    trunk.str = "\b"B_BL""B_HR""B_HR;
    prev->str = prev_str;
  }

  show_trunks(&trunk);
  printf(B_HR"\u2588");
  (*pf)(bst);
  printf("\n");

  if (prev) prev->str = prev_str;
  trunk.str = "   "B_VT;

  bst_print(get_right(bst), &trunk, pf);
  if (!prev) puts("");
}
