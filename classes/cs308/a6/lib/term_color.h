#ifndef _LIB_TERM_COLOR_H
#define _LIB_TERM_COLOR_H

#ifdef _USE_COLOR_TERM

  /* Reset */
  #define C_OFF           "\e[0m"       // Text Reset

  /* Regular Colors */
  #define C_BLACK         "\e[0;30m"    // Black
  #define C_RED           "\e[0;31m"    // Red
  #define C_GREEN         "\e[0;32m"    // Green
  #define C_YELLOW        "\e[0;33m"    // Yellow
  #define C_BLUE          "\e[0;34m"    // Blue
  #define C_PURPLE        "\e[0;35m"    // Purple
  #define C_CYAN          "\e[0;36m"    // Cyan
  #define C_WHITE         "\e[0;37m"    // White

  /* Bold */
  #define C_BBLACK        "\e[1;30m"    // Black
  #define C_BRED          "\e[1;31m"    // Red
  #define C_BGREEN        "\e[1;32m"    // Green
  #define C_BYELLOW       "\e[1;33m"    // Yellow
  #define C_BBLUE         "\e[1;34m"    // Blue
  #define C_BPURPLE       "\e[1;35m"    // Purple
  #define C_BCYAN         "\e[1;36m"    // Cyan
  #define C_BWHITE        "\e[1;37m"    // White

  /* Underline */
  #define C_UBlack        "\e[4;30m"    // Black
  #define C_URed          "\e[4;31m"    // Red
  #define C_UGreen        "\e[4;32m"    // Green
  #define C_UYellow       "\e[4;33m"    // Yellow
  #define C_UBlue         "\e[4;34m"    // Blue
  #define C_UPurple       "\e[4;35m"    // Purple
  #define C_UCyan         "\e[4;36m"    // Cyan
  #define C_UWhite        "\e[4;37m"    // White

  /* Background */
  #define C_On_Black      "\e[40m"      // Black
  #define C_On_Red        "\e[41m"      // Red
  #define C_On_Green      "\e[42m"      // Green
  #define C_On_Yellow     "\e[43m"      // Yellow
  #define C_On_Blue       "\e[44m"      // Blue
  #define C_On_Purple     "\e[45m"      // Purple
  #define C_On_Cyan       "\e[46m"      // Cyan
  #define C_On_White      "\e[47m"      // White

  /* High Intensity */
  #define C_IBlack        "\e[0;90m"    // Black
  #define C_IRed          "\e[0;91m"    // Red
  #define C_IGreen        "\e[0;92m"    // Green
  #define C_IYellow       "\e[0;93m"    // Yellow
  #define C_IBlue         "\e[0;94m"    // Blue
  #define C_IPurple       "\e[0;95m"    // Purple
  #define C_ICyan         "\e[0;96m"    // Cyan
  #define C_IWhite        "\e[0;97m"    // White

  /* Bold High Intensity */
  #define C_BIBlack       "\e[1;90m"    // Black
  #define C_BIRed         "\e[1;91m"    // Red
  #define C_BIGreen       "\e[1;92m"    // Green
  #define C_BIYellow      "\e[1;93m"    // Yellow
  #define C_BIBlue        "\e[1;94m"    // Blue
  #define C_BIPurple      "\e[1;95m"    // Purple
  #define C_BICyan        "\e[1;96m"    // Cyan
  #define C_BIWhite       "\e[1;97m"    // White

  /* High Intensity backgrounds */
  #define C_On_IBlack     "\e[0;100m"   // Black
  #define C_On_IRed       "\e[0;101m"   // Red
  #define C_On_IGreen     "\e[0;102m"   // Green
  #define C_On_IYellow    "\e[0;103m"   // Yellow
  #define C_On_IBlue      "\e[0;104m"   // Blue
  #define C_On_IPurple    "\e[0;105m"   // Purple
  #define C_On_ICyan      "\e[0;106m"   // Cyan
  #define C_On_IWhite     "\e[0;107m"   // White

#else

  /* Reset */
  #define C_OFF           ""    // Text Reset

  /* Regular Colors */
  #define C_BLACK         ""    // Black
  #define C_RED           ""    // Red
  #define C_GREEN         ""    // Green
  #define C_YELLOW        ""    // Yellow
  #define C_BLUE          ""    // Blue
  #define C_PURPLE        ""    // Purple
  #define C_CYAN          ""    // Cyan
  #define C_WHITE         ""    // White

  /* Bold */
  #define C_BBLACK        ""    // Black
  #define C_BRED          ""    // Red
  #define C_BGREEN        ""    // Green
  #define C_BYELLOW       ""    // Yellow
  #define C_BBLUE         ""    // Blue
  #define C_BPURPLE       ""    // Purple
  #define C_BCYAN         ""    // Cyan
  #define C_BWHITE        ""    // White

  /* Underline */
  #define C_UBlack        ""    // Black
  #define C_URed          ""    // Red
  #define C_UGreen        ""    // Green
  #define C_UYellow       ""    // Yellow
  #define C_UBlue         ""    // Blue
  #define C_UPurple       ""    // Purple
  #define C_UCyan         ""    // Cyan
  #define C_UWhite        ""    // White

  /* Background */
  #define C_On_Black      ""    // Black
  #define C_On_Red        ""    // Red
  #define C_On_Green      ""    // Green
  #define C_On_Yellow     ""    // Yellow
  #define C_On_Blue       ""    // Blue
  #define C_On_Purple     ""    // Purple
  #define C_On_Cyan       ""    // Cyan
  #define C_On_White      ""    // White

  /* High Intensity */
  #define C_IBlack        ""    // Black
  #define C_IRed          ""    // Red
  #define C_IGreen        ""    // Green
  #define C_IYellow       ""    // Yellow
  #define C_IBlue         ""    // Blue
  #define C_IPurple       ""    // Purple
  #define C_ICyan         ""    // Cyan
  #define C_IWhite        ""    // White

  /* Bold High Intensity */
  #define C_BIBlack       ""    // Black
  #define C_BIRed         ""    // Red
  #define C_BIGreen       ""    // Green
  #define C_BIYellow      ""    // Yellow
  #define C_BIBlue        ""    // Blue
  #define C_BIPurple      ""    // Purple
  #define C_BICyan        ""    // Cyan
  #define C_BIWhite       ""    // White

  /* High Intensity backgrounds */
  #define C_On_IBlack     ""     // Black
  #define C_On_IRed       ""     // Red
  #define C_On_IGreen     ""     // Green
  #define C_On_IYellow    ""     // Yellow
  #define C_On_IBlue      ""     // Blue
  #define C_On_IPurple    ""     // Purple
  #define C_On_ICyan      ""     // Cyan
  #define C_On_IWhite     ""     // White

#endif  // _USE_COLOR_TERM

#endif  // _LIB_TERM_COLOR_H
