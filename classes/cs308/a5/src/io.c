// io.c

#include "../lib/io.h"

static inline void tline(size_t width, size_t pad) {
  for (size_t i = 0; i < pad; i++)
    printf(" ");
  printf("%s", B_TL);
  for (size_t i = 0; i < width-2; i++)
    printf("%s", B_HR);
  printf("%s\n", B_TR);
}

static inline void bline(size_t width, size_t pad) {
  for (size_t i = 0; i < pad; i++)
    printf(" ");
  printf("%s", B_BL);
  for (size_t i = 0; i < width-2; i++)
    printf("%s", B_HR);
  printf("%s\n", B_BR);
}

void print_boxed(const char * label, size_t width, size_t pad) {
  char label_str[86];
  size_t inspadl = (width-strlen(label)-2) / 2;
  size_t inspadr = inspadl + (width-strlen(label)-2) % 2;
  size_t i = 0;
  for (size_t j = 0; j < pad; j++)
    label_str[i++] = ' ';
  label_str[i++] = 0xe2;
  label_str[i++] = 0x94;
  label_str[i++] = 0x82;
  for (size_t j = 0; j < inspadl; j++)
    label_str[i++] = ' ';
  for (size_t j = 0; j < strlen(label); j++)
    label_str[i++] = label[j];
  for (size_t j = 0; j < inspadr; j++)
    label_str[i++] = ' ';
  label_str[i++] = 0xe2;
  label_str[i++] = 0x94;
  label_str[i++] = 0x82;
  label_str[i++] = '\n';
  label_str[i++] = '\0';
  printf("\n");
  tline(width, pad);
  printf("%s", label_str);
  bline(width, pad);
}
