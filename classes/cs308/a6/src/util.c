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
  [DT_BLK]     = C_On_Black C_GREEN,
  [DT_CHR]     = C_On_Black C_YELLOW,
  [DT_DIR]     = C_On_Black C_BIBlue,
  [DT_FIFO]    = C_On_Black C_PURPLE,
  [DT_LNK]     = C_On_Black C_CYAN,
  [DT_REG]     = C_On_Black C_BIWhite,
  [DT_SOCK]    = C_On_Black C_RED,
  [DT_UNKNOWN] = C_On_Red C_BIWhite
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
    struct stat file_stat;
    fsys_node_t * f_info = malloc(sizeof(fsys_node_t));
    if (f_info == NULL) {
      perror("malloc");
      exit(EXIT_FAILURE);
    }

    char * name = entry->d_name;
    if (stat(name, &file_stat) == -1) {
      perror("stat");
      exit(EXIT_FAILURE);
    }
    snprintf(f_info->d_name, NAME_MAX, "%s", name);

    f_info->d_ino      = entry->d_ino;
    f_info->d_off      = entry->d_off;
    f_info->d_reclen   = entry->d_reclen;
    f_info->d_type     = entry->d_type;
    f_info->depth      = depth;
    f_info->st_dev     = file_stat.st_dev;
    f_info->dev_maj    = major(file_stat.st_dev);
    f_info->dev_min    = minor(file_stat.st_dev);
    f_info->st_ino     = file_stat.st_ino;
    f_info->st_mode    = file_stat.st_mode;
    f_info->st_nlink   = file_stat.st_nlink;
    f_info->st_uid     = file_stat.st_uid;
    f_info->st_gid     = file_stat.st_gid;
    f_info->st_rdev    = file_stat.st_rdev;
    f_info->st_size    = file_stat.st_size;
    f_info->st_blksize = file_stat.st_blksize;
    f_info->st_blocks  = file_stat.st_blocks;
    f_info->st_atim    = file_stat.st_atim;
    f_info->st_mtim    = file_stat.st_mtim;
    f_info->st_ctim    = file_stat.st_ctim;

    entries          = list_pre(entries, f_info);
  }
  if (closedir(dir) == -1) {
    perror("closedir");
    exit(EXIT_FAILURE);
  }
  return entries;
}

/****************************************************************************/
static inline const char * int_to_binary(unsigned int x) {
    static char b[33];
    b[0] = '\0';
    for (unsigned int z = INT_MAX/2+1; z > 0; z >>= 1) {
      strcat(b, ((x & z) == z) ? "1" : "0");
    }
    return b;
}

/****************************************************************************/
void display_fs_node(void * node_addr) {
  fsys_node_t * f_info = (fsys_node_t *)node_addr;

  char os[f_info->depth+1];
  memset(os, ' ', f_info->depth);
  os[f_info->depth] = '\0';

  int    type = f_info->d_type;
  mode_t mode = f_info->st_mode;
  char   mstr[13];
  memset(mstr, '|', 12);
  mstr[12] = '\0';

  mstr[0] = S_ISDIR(mode)     ? 'd' : '-';

  mstr[2]  = (mode & S_IRUSR) ? 'r' : '-';
  mstr[3]  = (mode & S_IWUSR) ? 'w' : '-';
  mstr[4]  = (mode & S_IXUSR) ? 'x' : '-';

  mstr[6]  = (mode & S_IRGRP) ? 'r' : '-';
  mstr[7]  = (mode & S_IWGRP) ? 'w' : '-';
  mstr[8]  = (mode & S_IXGRP) ? 'x' : '-';

  mstr[10] = (mode & S_IROTH) ? 'r' : '-';
  mstr[11] = (mode & S_IWOTH) ? 'w' : '-';
  mstr[12] = (mode & S_IXOTH) ? 'x' : '-';

  struct passwd * pw = getpwuid(f_info->st_uid);
  if (pw == NULL) {
    perror("getpwuid");
    exit(EXIT_FAILURE);
  }

  char * user_name = pw->pw_name;
  char * user_pw   = pw->pw_passwd;
  char * user_info = pw->pw_gecos;
  char * user_home = pw->pw_dir;
  char * user_shll = pw->pw_shell;

  struct group * gr = getgrgid(f_info->st_gid);
  if (gr == NULL) {
    perror("getgrgid");
    exit(EXIT_FAILURE);
  }

  char *  gr_name = gr->gr_name;
  char *  gr_pw   = gr->gr_passwd;
  char ** gr_mem  = gr->gr_mem;

  printf("%s%s %s %s\n", os, type_colors[type], f_info->d_name, C_OFF);
  printf("%s d_ino       = %ld\n", os, f_info->d_ino);
  printf("%s d_off       = %ld\n", os, f_info->d_off);
  printf("%s d_reclen    = %u\n",  os, f_info->d_reclen);
  printf("%s d_type      = %s\n",  os, type_names[type]);
  printf("%s dev_maj     = %u\n",  os, f_info->dev_maj);
  printf("%s dev_min     = %u\n",  os, f_info->dev_min);
  printf("%s st_ino      = %ld\n", os, f_info->st_ino);
  printf("%s st_mode     = %u\n",  os, f_info->st_mode);
  printf("%s mstr        = %s\n",  os, mstr);
  printf("%s st_uid      = %d\n",  os, f_info->st_uid);
  printf("%s user_name   = %s\n",  os, user_name);
  printf("%s user_pw     = %s\n",  os, user_pw);
  printf("%s user_info   = %s\n",  os, user_info);
  printf("%s user_home   = %s\n",  os, user_home);
  printf("%s user_shll   = %s\n",  os, user_shll);
  printf("%s gr_name     = %s\n",  os, gr_name);
  printf("%s gr_pw       = %s\n",  os, gr_pw);
  printf("%s gr_mem[0]   = %s\n",  os, gr_mem[0]);
  printf("%s st_rdev     = %lu\n", os, f_info->st_rdev);
  printf("%s st_rdev_maj = %u\n",  os, major(f_info->st_rdev));
  printf("%s st_rdev_min = %u\n",  os, minor(f_info->st_rdev));
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
