// io.h

#ifndef LIB_IO_H_
#define LIB_IO_H_

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

/******************************************************************************/
void print_boxed(const char * label, size_t width, size_t pad);

#endif  // LIB_IO_H_
