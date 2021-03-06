#include "lib/util.h"

bool is_file(const char * path);

int main(int argc, char *argv[]) {
  if (argc == 1) {
    list_t * entries = dir_list(".", 0);
    list_iter(entries, &display_fs_node);
    list_iter(entries, &free);
    list_dispose(entries);

  } else {
    if (strcmp(argv[1], "--setup") == 0) {
      create_test_files();
    } else if (strcmp(argv[1], "--help") == 0) {
      display_usage(argv[0]);
    } else {
      char ret_dir[1024];
      getcwd(ret_dir, sizeof(ret_dir));
      
      for (int i = 1; i < argc; i++) {
        if (is_dir(argv[i])) {
          const char * dir_name = argv[i];
          display_label(dir_name);
          chdir(dir_name);
          list_t * entries = dir_list(".", 2);
          list_iter(entries, &display_fs_node);
          list_iter(entries, &free);
          list_dispose(entries);
          chdir(ret_dir);
          printf("\n");

        } else {
          const char * file_name = argv[i];
          fsys_node_t * f_info = file_list(file_name, 0);
          display_fs_node(f_info);
        }
      }
    }
  }
  exit(EXIT_SUCCESS);
}



/* EXAMPLE */
/*******************************************/
/* FILENAME:                  alpha */
/* FILE_TYPE:                 ordinary */
/* PERMISSIONS:               rw- r-- r-- */
/* OWNER_NAME:                jedwards */
/* GROUP_NAM:                 grad */
/* DATE_OF_LAST_MODIFICATION: Mar 30 08:11 2003 */
/* LINK_COUNT:                2 */
/* SIZE_IN_BYTES:             1345 (or 12, 6 dev info) */
/* INODE_NUMBER:              347  */
