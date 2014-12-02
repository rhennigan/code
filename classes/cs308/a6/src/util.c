#include "../lib/util.h"

const char * type_names[] = {
  [DT_BLK]     = "block device",
  [DT_CHR]     = "character device",
  [DT_DIR]     = "directory",
  [DT_FIFO]    = "named pipe (FIFO)",
  [DT_LNK]     = "symbolic link",
  [DT_REG]     = "regular file",
  [DT_SOCK]    = "UNIX domain socket",
  [DT_UNKNOWN] = "unknown"
};

const char * type_colors[] = {
  [DT_BLK]     = C_GREEN,
  [DT_CHR]     = C_YELLOW,
  [DT_DIR]     = C_BBLUE,
  [DT_FIFO]    = C_PURPLE,
  [DT_LNK]     = C_CYAN,
  [DT_REG]     = C_WHITE,
  [DT_SOCK]    = C_RED,
  [DT_UNKNOWN] = C_BRED
};

/****************************************************************************/
list_t * dir_list(char * dir_name, size_t depth) {
  DIR * dir = opendir(dir_name);
  if (!dir) {
    perror("dir_list opendir");
    exit(EXIT_FAILURE);
  }
  list_t * entries = NULL;
  struct dirent * entry;
  while ((entry = readdir(dir)) != NULL) {
    struct stat fstat;
    fsys_node_t * node = malloc(sizeof(fsys_node_t));
    if (node == NULL) {
      perror("malloc");
      exit(EXIT_FAILURE);
    }

    char * name = entry->d_name;
    if (stat(name, &fstat) == -1) {
      perror("stat");
      exit(EXIT_FAILURE);
    }
    snprintf(node->d_name, NAME_MAX, "%s", name);

    node->d_ino      = entry->d_ino;
    node->d_off      = entry->d_off;
    node->d_reclen   = entry->d_reclen;
    node->d_type     = entry->d_type;
    node->depth      = depth;
    entries          = list_pre(entries, node);
  }
  if (closedir(dir) == -1) {
    perror("closedir");
    exit(EXIT_FAILURE);
  }
  return entries;
}

/****************************************************************************/
void display_fs_node(void * node_addr) {
  fsys_node_t * node = (fsys_node_t *)node_addr;

  char os[node->depth+1];
  memset(os, ' ', node->depth);
  os[node->depth] = '\0';

  int type = node->d_type;

  printf("%s%s%s%s\n",          os, type_colors[type], node->d_name, C_OFF);
  printf("%s d_ino    = %ld\n", os, node->d_ino);
  printf("%s d_off    = %ld\n", os, node->d_off);
  printf("%s d_reclen = %u\n",  os, node->d_reclen);
  printf("%s d_type   = %s\n",  os, type_names[type]);
  printf("\n");
}

/****************************************************************************/
bool name_cmp(void * a, void * b) {
  fsys_node_t * node1 = a;
  fsys_node_t * node2 = b;
  char * str1  = node1->d_name;
  char * str2  = node2->d_name;
  bool   cmp   = node1->d_type == node2->d_type ?
                 strcmp(str1, str2) < 1 :
                 node1->d_type < node2->d_type;
  return cmp;
}
