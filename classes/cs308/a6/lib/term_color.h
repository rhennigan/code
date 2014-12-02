#ifndef _LIB_TERM_COLOR_H
#define _LIB_TERM_COLOR_H

#ifdef _USE_COLOR_TERM

  /* Reset */
  #define Color_Off     "\e[0m"       // Text Reset

  /* Regular Colors */
  #define Black         "\e[0;30m"    // Black
  #define Red           "\e[0;31m"    // Red
  #define Green         "\e[0;32m"    // Green
  #define Yellow        "\e[0;33m"    // Yellow
  #define Blue          "\e[0;34m"    // Blue
  #define Purple        "\e[0;35m"    // Purple
  #define Cyan          "\e[0;36m"    // Cyan
  #define White         "\e[0;37m"    // White

  /* Bold */
  #define BBlack        "\e[1;30m"    // Black
  #define BRed          "\e[1;31m"    // Red
  #define BGreen        "\e[1;32m"    // Green
  #define BYellow       "\e[1;33m"    // Yellow
  #define BBlue         "\e[1;34m"    // Blue
  #define BPurple       "\e[1;35m"    // Purple
  #define BCyan         "\e[1;36m"    // Cyan
  #define BWhite        "\e[1;37m"    // White

  /* Underline */
  #define UBlack        "\e[4;30m"    // Black
  #define URed          "\e[4;31m"    // Red
  #define UGreen        "\e[4;32m"    // Green
  #define UYellow       "\e[4;33m"    // Yellow
  #define UBlue         "\e[4;34m"    // Blue
  #define UPurple       "\e[4;35m"    // Purple
  #define UCyan         "\e[4;36m"    // Cyan
  #define UWhite        "\e[4;37m"    // White

  /* Background */
  #define On_Black      "\e[40m"      // Black
  #define On_Red        "\e[41m"      // Red
  #define On_Green      "\e[42m"      // Green
  #define On_Yellow     "\e[43m"      // Yellow
  #define On_Blue       "\e[44m"      // Blue
  #define On_Purple     "\e[45m"      // Purple
  #define On_Cyan       "\e[46m"      // Cyan
  #define On_White      "\e[47m"      // White

  /* High Intensity */
  #define IBlack        "\e[0;90m"    // Black
  #define IRed          "\e[0;91m"    // Red
  #define IGreen        "\e[0;92m"    // Green
  #define IYellow       "\e[0;93m"    // Yellow
  #define IBlue         "\e[0;94m"    // Blue
  #define IPurple       "\e[0;95m"    // Purple
  #define ICyan         "\e[0;96m"    // Cyan
  #define IWhite        "\e[0;97m"    // White

  /* Bold High Intensity */
  #define BIBlack       "\e[1;90m"    // Black
  #define BIRed         "\e[1;91m"    // Red
  #define BIGreen       "\e[1;92m"    // Green
  #define BIYellow      "\e[1;93m"    // Yellow
  #define BIBlue        "\e[1;94m"    // Blue
  #define BIPurple      "\e[1;95m"    // Purple
  #define BICyan        "\e[1;96m"    // Cyan
  #define BIWhite       "\e[1;97m"    // White

  /* High Intensity backgrounds */
  #define On_IBlack     "\e[0;100m"   // Black
  #define On_IRed       "\e[0;101m"   // Red
  #define On_IGreen     "\e[0;102m"   // Green
  #define On_IYellow    "\e[0;103m"   // Yellow
  #define On_IBlue      "\e[0;104m"   // Blue
  #define On_IPurple    "\e[0;105m"   // Purple
  #define On_ICyan      "\e[0;106m"   // Cyan
  #define On_IWhite     "\e[0;107m"   // White

#else

  /* Reset */
  #define Color_Off     ""    // Text Reset

  /* Regular Colors */
  #define Black         ""    // Black
  #define Red           ""    // Red
  #define Green         ""    // Green
  #define Yellow        ""    // Yellow
  #define Blue          ""    // Blue
  #define Purple        ""    // Purple
  #define Cyan          ""    // Cyan
  #define White         ""    // White

  /* Bold */
  #define BBlack        ""    // Black
  #define BRed          ""    // Red
  #define BGreen        ""    // Green
  #define BYellow       ""    // Yellow
  #define BBlue         ""    // Blue
  #define BPurple       ""    // Purple
  #define BCyan         ""    // Cyan
  #define BWhite        ""    // White

  /* Underline */
  #define UBlack        ""    // Black
  #define URed          ""    // Red
  #define UGreen        ""    // Green
  #define UYellow       ""    // Yellow
  #define UBlue         ""    // Blue
  #define UPurple       ""    // Purple
  #define UCyan         ""    // Cyan
  #define UWhite        ""    // White

  /* Background */
  #define On_Black      ""    // Black
  #define On_Red        ""    // Red
  #define On_Green      ""    // Green
  #define On_Yellow     ""    // Yellow
  #define On_Blue       ""    // Blue
  #define On_Purple     ""    // Purple
  #define On_Cyan       ""    // Cyan
  #define On_White      ""    // White

  /* High Intensity */
  #define IBlack        ""    // Black
  #define IRed          ""    // Red
  #define IGreen        ""    // Green
  #define IYellow       ""    // Yellow
  #define IBlue         ""    // Blue
  #define IPurple       ""    // Purple
  #define ICyan         ""    // Cyan
  #define IWhite        ""    // White

  /* Bold High Intensity */
  #define BIBlack       ""    // Black
  #define BIRed         ""    // Red
  #define BIGreen       ""    // Green
  #define BIYellow      ""    // Yellow
  #define BIBlue        ""    // Blue
  #define BIPurple      ""    // Purple
  #define BICyan        ""    // Cyan
  #define BIWhite       ""    // White

  /* High Intensity backgrounds */
  #define On_IBlack     ""     // Black
  #define On_IRed       ""     // Red
  #define On_IGreen     ""     // Green
  #define On_IYellow    ""     // Yellow
  #define On_IBlue      ""     // Blue
  #define On_IPurple    ""     // Purple
  #define On_ICyan      ""     // Cyan
  #define On_IWhite     ""     // White

#endif  // _USE_COLOR_TERM

#endif  // _LIB_TERM_COLOR_H
