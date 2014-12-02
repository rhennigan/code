#include "lib/util.h"

int main(int argc, char *argv[]) {
  char   * dir_name = ".";
  list_t * unsorted_entries = dir_list(dir_name, 2);
  list_t * entries = list_sort(unsorted_entries, &name_cmp);
  list_iter(entries, &display_fs_node);
  return 0;
}
