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
  [DT_BLK]     = C_BIGreen,
  [DT_CHR]     = C_BIYellow,
  [DT_DIR]     = C_BIBlue,
  [DT_FIFO]    = C_BIPurple,
  [DT_LNK]     = C_BICyan,
  [DT_REG]     = C_BIWhite,
  [DT_SOCK]    = C_BIRed,
  [DT_UNKNOWN] = C_On_Red C_BIWhite
};

enum units {
  BYTES,
  KBYTES,
  MBYTES,
  GBYTES
};

const char * units[] = {
  [BYTES]  = C_GREEN            "B"  C_OFF,
  [KBYTES] = C_YELLOW           "KB" C_OFF,
  [MBYTES] = C_RED              "MB" C_OFF,
  [GBYTES] = C_On_Red C_BIWhite "GB" C_OFF
};

#define MIN(a, b) ((a) < (b) ? (a) : (b))

/****************************************************************************/
static inline unsigned char fix_type(mode_t m) {
  mode_t masked = m & S_IFMT;
  return masked == S_IFREG ? DT_REG
       : masked == S_IFDIR ? DT_DIR
       : masked == S_IFCHR ? DT_CHR
       : masked == S_IFBLK ? DT_BLK
       : masked == S_IFIFO ? DT_FIFO
       : masked == S_IFLNK ? DT_LNK
       : masked == S_IFSOCK ? DT_SOCK
       : DT_UNKNOWN;
}

/****************************************************************************/
static inline char * byte_str(unsigned long b) {
  static char str[80];
  unsigned long i = 0;
  while (b > 9999) {
    i++;
    b /= 1024;
  }
  snprintf(str, 80, "%lu%s", b, units[i]);
  return str;
}

/****************************************************************************/
list_t * dir_list(const char * d_name, size_t depth) {
  printf("dir_list(%s, %lu)\n", d_name, depth);
  fflush(NULL);
  const char * dir_name = d_name;
  const size_t cdepth = depth;
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

    size_t len = strlen(dir_name);
    char path[len+2];
    snprintf(path, len+1, "%s", dir_name);
    path[len]   = '/';
    path[len+1] = '\0';

    char * name = strcat(path, entry->d_name);

    if (stat(name, &file_stat) == -1) {
      perror("lstat");
      exit(EXIT_FAILURE);
    }

    snprintf(f_info->d_name, NAME_MAX, "%s", name);

    f_info->d_ino      = entry->d_ino;
    f_info->d_off      = entry->d_off;
    f_info->d_reclen   = entry->d_reclen;
    f_info->d_type     = fix_type(file_stat.st_mode);
    f_info->depth      = MIN(20, cdepth);
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
    f_info->atime      = file_stat.st_atime;
    f_info->mtime      = file_stat.st_mtime;
    f_info->ctime      = file_stat.st_ctime;

    size_t nlen = strlen(name);

    if (cdepth <= 8 && S_ISDIR(f_info->st_mode) &&
        !(name[nlen-1] == '.' &&
         (name[nlen-2] == '/' ||
         (name[nlen-2] == '.' &&
          name[nlen-3] == '/')))) {
      const char * dlname = f_info->d_name;
      f_info->sub_nodes = dir_list(dlname, cdepth+2);
    } else {
      f_info->sub_nodes = NULL;
    }

    entries = list_pre(entries, f_info);
  }

  if (closedir(dir) == -1) {
    perror("closedir");
    exit(EXIT_FAILURE);
  }

  list_t * sorted = list_sort(entries, &name_cmp);
  return sorted;
}

/****************************************************************************/
const char * vert = C_BIWhite B_VT C_OFF;

static inline void pv(size_t depth) {
  size_t i;
  for (i = 0; i < depth / 2; i++)
    printf(" %s", vert);
}

static inline bool ndir(fsys_node_t * f_info) {
  size_t nlen = strlen(f_info->d_name);
  return S_ISDIR(f_info->st_mode) &&
         !(f_info->d_name[nlen-1] == '.' &&
          (f_info->d_name[nlen-2] == '/' ||
          (f_info->d_name[nlen-2] == '.' &&
           f_info->d_name[nlen-3] == '/')));
}

/****************************************************************************/
void display_fs_node(void * node_addr) {
  fsys_node_t * f_info = (fsys_node_t *)node_addr;

  char os[40];
  memset(os, ' ', 40);
  size_t i;
  for (i = 0; i < f_info->depth; i+=2) {
    os[i] = '|';
  }
  os[39] = '\0';
  os[f_info->depth] = '\0';

  int    type     = f_info->d_type;
  mode_t mode     = f_info->st_mode;
  char   mstr[11] = "          ";

  mstr[0] = S_ISDIR(mode)    ? 'd' : '-';

  mstr[1] = (mode & S_IRUSR) ? 'r' : '-';
  mstr[2] = (mode & S_IWUSR) ? 'w' : '-';
  mstr[3] = (mode & S_IXUSR) ? 'x' : '-';

  mstr[4] = (mode & S_IRGRP) ? 'r' : '-';
  mstr[5] = (mode & S_IWGRP) ? 'w' : '-';
  mstr[6] = (mode & S_IXGRP) ? 'x' : '-';

  mstr[7] = (mode & S_IROTH) ? 'r' : '-';
  mstr[8] = (mode & S_IWOTH) ? 'w' : '-';
  mstr[9] = (mode & S_IXOTH) ? 'x' : '-';

  struct passwd * pw = getpwuid(f_info->st_uid);
  if (pw == NULL) {
    perror("getpwuid");
    exit(EXIT_FAILURE);
  }

  char * user_name = pw->pw_name;
  /* char * user_pw   = pw->pw_passwd; */
  /* char * user_info = pw->pw_gecos; */
  /* char * user_home = pw->pw_dir; */
  /* char * user_shll = pw->pw_shell; */

  struct group * gr = getgrgid(f_info->st_gid);
  if (gr == NULL) {
    perror("getgrgid");
    exit(EXIT_FAILURE);
  }

  char *  gr_name = gr->gr_name;
  /* char *  gr_pw   = gr->gr_passwd; */
  /* char ** gr_mem  = gr->gr_mem; */

  bool exec_b = (mode & S_IXUSR) || (mode & S_IXGRP) || (mode & S_IXOTH);

  const char * leftc     = ndir(f_info) ? B_TL : " ";
  const char * lbl_bg    = ndir(f_info) ? C_On_Blue : C_On_Black;
  const char * lbl_color = ndir(f_info) ? C_BIWhite :
                           (type == DT_REG && exec_b) ?
                           C_BIGreen :
                           type_colors[type];
  size_t b = 2;
  for (i = b; i < strlen(f_info->d_name); i++)
    b = f_info->d_name[i] == '/' ? i + 1: b;

  pv(f_info->depth);
  printf(" %s%s%s %-16s %s", lbl_bg, lbl_color, leftc, f_info->d_name + b, C_OFF);
  printf(" %s%s%s", lbl_color, type_names[type], C_OFF);
  printf(" %s", ctime(&f_info->mtime));
  pv(f_info->depth);
  if (ndir(f_info)) pv(2);
  printf(" %s", mstr);
  printf(" %s", user_name);
  printf(" %s", gr_name);
  printf(" %lu", f_info->st_nlink);
  printf(" %s", byte_str(f_info->st_size));
  printf(" %lu", (unsigned long)f_info->st_ino);
  
  /* printf("%s d_off       = %ld\n", os, f_info->d_off); */
  /* printf("%s d_reclen    = %u\n",  os, f_info->d_reclen); */
  /* printf("%s d_type      = %s\n",  os, type_names[type]); */
  /* printf("%s dev_maj     = %u\n",  os, f_info->dev_maj); */
  /* printf("%s dev_min     = %u\n",  os, f_info->dev_min); */
  /* printf("%s st_ino      = %ld\n", os, f_info->st_ino); */
  /* printf("%s st_mode     = %u\n",  os, f_info->st_mode); */
  /* printf("%s   mstr        = %s\n",  os, mstr); */
  /* printf("%s st_uid      = %d\n",  os, f_info->st_uid); */
  /* printf("%s   user_name   = %s\n",  os, user_name); */
  /* printf("%s user_pw     = %s\n",  os, user_pw); */
  /* printf("%s user_info   = %s\n",  os, user_info); */
  /* printf("%s user_home   = %s\n",  os, user_home); */
  /* printf("%s user_shll   = %s\n",  os, user_shll); */
  /* printf("%s   gr_name     = %s\n",  os, gr_name); */
  /* printf("%s gr_pw       = %s\n",  os, gr_pw); */
  /* printf("%s gr_mem[0]   = %s\n",  os, gr_mem[0]); */
  /* printf("%s st_rdev     = %lu\n", os, f_info->st_rdev); */
  /* printf("%s st_rdev_maj = %u\n",  os, major(f_info->st_rdev)); */
  /* printf("%s st_rdev_min = %u\n",  os, minor(f_info->st_rdev)); */
  /* printf("%s st_blksize  = %lu\n", os, f_info->st_blksize); */
  /* printf("%s st_blocks   = %lu\n", os, f_info->st_blocks); */
  /* printf("%s atime       = %s",    os, ctime(&f_info->atime)); */
  /* printf("%s   mtime       = %s",    os, ctime(&f_info->mtime)); */
  /* printf("%s   st_nlink    = %lu\n", os, f_info->st_nlink); */
  /* printf("%s   st_size     = %lu\n", os, f_info->st_size); */
  /* printf("%s   d_ino       = %ld\n", os, f_info->d_ino); */
  /* printf("%s ctime       = %s",    os, ctime(&f_info->ctime)); */
  /* printf("%s sub_nodes   = %p\n",  os, f_info->sub_nodes); */
  printf("\n");

  if (f_info->sub_nodes != NULL) {
    list_iter(f_info->sub_nodes, &display_fs_node);
    pv(f_info->depth);
    printf(" %s", C_BIWhite B_BL);
    size_t i;
    for (i = 0; i < 58; i++)
      printf("%s", B_HR);
    printf("%s\n", C_OFF);
  }
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

/****************************************************************************/

