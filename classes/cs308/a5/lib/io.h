// io.h

#ifndef LIB_IO_H_
#define LIB_IO_H_

#define USE_COLOR_TERM

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/******************************************************************************/
/* UNICODE CHARACTERS FOR BOX DRAWING                                         */
/******************************************************************************/

#define B_HR "\u2500"  // horizontal bar
#define B_TL "\u250C"  // top-left box corner
#define B_TR "\u2510"  // top-right box corner
#define B_BL "\u2514"  // bottom-left box corner
#define B_BR "\u2518"  // bottom-right box corner
#define B_VT "\u2502"  // vertical bar
#define B_LM "\u251C"  // left-middle join
#define B_RM "\u2524"  // right-middle join
#define B_TM "\u252C"  // top-middle join
#define B_BM "\u2534"  // bottom-middle join
#define B_CM "\u253C"  // center-middle join

/******************************************************************************/
/* COLOR DEFINITIONS FOR TERMINAL OUTPUT                                      */
/******************************************************************************/
#ifdef USE_COLOR_TERM
  #define C_RED     "\x1b[31m"
  #define C_GREEN   "\x1b[32m"
  #define C_YELLOW  "\x1b[33m"
  #define C_BLUE    "\x1b[34m"
  #define C_MAGENTA "\x1b[35m"
  #define C_CYAN    "\x1b[36m"
  #define C_RESET   "\x1b[0m"
#else
  #define C_RED     ""
  #define C_GREEN   ""
  #define C_YELLOW  ""
  #define C_BLUE    ""
  #define C_MAGENTA ""
  #define C_CYAN    ""
  #define C_RESET   ""
#endif

#define WAIT() do {                                     \
    char ch;                                            \
    printf("Press [ENTER] to continue...");             \
    fflush(stdout);                                     \
    while ((ch = getchar()) != '\n' && ch != EOF) {}    \
  } while (0);

/******************************************************************************/
void print_boxed(const char * label, size_t width, size_t pad);

#endif  // LIB_IO_H_
