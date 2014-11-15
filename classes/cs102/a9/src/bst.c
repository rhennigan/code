// bst.c - binary search tree implemented as an AVL tree
// Copyright (C) 2014 Richard Hennigan

#include "../lib/bst.h"

#define MAX(a, b) ((a) > (b) ? (a) : (b))

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
  if (has_parent(bst)) {
    set_depth(bst, get_depth(get_parent(bst)) + 1);
  } else {
    set_depth(bst, 0);
  }
  if (has_left(bst)) {
    bst_update_depth(get_left(bst));
  }
  if (has_right(bst)) {
    bst_update_depth(get_right(bst));
  }
}

size_t force_depth(bst_t * bst) {
  if (bst == NULL) {
    return 0;
  } else if (is_leaf(bst)) {
    if (has_parent(bst)) {
      set_depth(bst, 0);
    }
    return 0;
  } else {
    size_t ld = force_depth(get_left(bst));
    size_t rd = force_depth(get_right(bst));
    size_t d = 1 + MAX(ld, rd);
    set_depth(bst, d);
    return d;
  }
}

static void rotate_left(bst_t ** bst) {
  bst_t * root = *bst;
  set_depth(root, get_depth(root) - 1);
  bst_t * pivot = get_right(root);
  set_depth(pivot, get_depth(pivot) + 1);
  set_right(root, get_left(pivot));
  set_left(pivot, root);
  *bst = pivot;
}

static void rotate_right(bst_t ** bst) {
  bst_t * root = *bst;
  set_depth(root, get_depth(root) - 1);
  bst_t * pivot = get_left(root);
  set_depth(pivot, get_depth(pivot) + 1);
  set_left(root, get_right(pivot));
  set_right(pivot, root);
  *bst = pivot;
}

static void inc_p_path(bst_t * bst) {
  size_t d;
  while (has_parent(bst)) {
    d = get_depth(bst);
    bst = get_parent(bst);
    if (d == get_depth(bst)) set_depth(bst, get_depth(bst) + 1);
  }
}

/******************************************************************************/
/* PUBLIC FUNCTIONS                                                           */
/******************************************************************************/

size_t bst_depth(bst_t * bst) {
  return get_depth(bst);
}

void bst_dispose(bst_t * bst);

void bst_dump(bst_t * bst, order_t order);

void bst_flatten(bst_t * bst, list_t ** list, order_t order);

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
    printf("td = NULL\n");
    set_data(bst, data);
    return;
  }
  int32_t diff = (*cmp)(data, td);
  if (diff == 0) {
    printf("td is duplicate\n");
    return;
  } else {  // (diff != 0)
    bool goleft = diff < 0 ? true : false;
    bst_t * next = goleft ? get_left(bst) : get_right(bst);
    if (next == NULL) {
      next = bst_init();  // new pointer, need to update parent
      goleft ? set_left(bst, next) : set_right(bst, next);
      set_parent(next, bst);
      set_data(next, data);
      inc_p_path(next);
      return;
    } else {  // (next != NULL)
      bst_insert(next, data, cmp);
    }  // endif (next == NULL)
  }  // endif (diff == 0)
}

void bst_print(bst_t * bst, pr_fun pf) {
  if (bst == NULL) return;
  bst_print(get_left(bst), pf);
  (*pf)(bst);
  bst_print(get_right(bst), pf);
}

void    bst_remove(bst_t * bst, void * get_data, cmp_fun cmp);

void *  bst_search(bst_t * bst, void * get_data, void * result, cmp_fun cmp);

void show_trunks(struct trunk * p) {
  if (!p) return;
  show_trunks(p->prev);
  printf("%s", p->str);
}

#define B_HR "\u2500"
#define B_TL "\u250C"
#define B_TR "\u2510"
#define B_BL "\u2514"
#define B_BR "\u2518"
#define B_VT "\u2502"

void show_tree(bst_t *root, struct trunk *prev) {
  if (root == NULL) return;
  struct trunk this_disp = { prev, "    " };
  char *prev_str = this_disp.str;
  show_tree(get_left(root), &this_disp);

  if (!prev) {
    this_disp.str = "---";
  } else if (is_left(root)) {
    this_disp.str = ".--";
    prev_str = "   |";
  } else {
    this_disp.str = "`--";
    prev->str = prev_str;
  }

  show_trunks(&this_disp);
  printf("%d\n", *(int*)get_data(root));

  if (prev) prev->str = prev_str;
  this_disp.str = "   |";

  show_tree(get_right(root), &this_disp);
  if (!prev) puts("");
}
