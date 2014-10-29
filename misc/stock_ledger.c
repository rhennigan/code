// src/stock_ledger.c - Copyright 2014, Richard Hennigan

#define CURL_STATICLIB

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <curl/curl.h>
#include <math.h>
#include "../lib/deque.h"
#include "../lib/user_input.h"

#define PI 3.14159
#define GK_RAD 5
#define GK_SIG 2.0

#define URL_SIZE 512
#define DATA_LEN 148
#define MARKET_SIZE 6

#define C_RED     "\x1b[31m"
#define C_GREEN   "\x1b[32m"
#define C_YELLOW  "\x1b[33m"
#define C_BLUE    "\x1b[34m"
#define C_MAGENTA "\x1b[35m"
#define C_CYAN    "\x1b[36m"
#define C_RESET   "\x1b[0m"

typedef struct market_data_s {
  char symbol[5];
  char name[BUFSIZ];
  double * data;
  double * smooth_data;
} market_data_t;

typedef struct ledger_entry_s {
  unsigned int id;
  char symbol[5];
  unsigned int shares;
  double purchase_price;
} ledger_entry_t;

double show_menu(market_data_t * market, int day, deque_t * ledger,
                 double funds);
const char* getfield(char* line, int num);
void download_data(char * symbol);
double * import_data(char * symbol);
double * gaussian_kernel(size_t radius, double sig);
double * convolved_data(double * data);
double derivative(double * data, int day, int n);
void purchase(int id, int shares, double price, deque_t * ledger, bool front,
              market_data_t * market);


int main(/* int argc, char *argv[] */) {
  char stock_id[][2][BUFSIZ] = {
    { "Google", "GOOG" },
    { "Apple", "AAPL" },
    { "Microsoft", "MSFT" },
    { "Netflix", "NFLX" },
    { "Amazon", "AMZN" },
    { "LinkedIn", "LNKD" } };

  market_data_t market[MARKET_SIZE];
  int i;
  for (i = 0; i < MARKET_SIZE; i ++) {
    printf("\n loading data for symbol: %s (%s)\n",
           stock_id[i][1], stock_id[i][0]);
    snprintf(market[i].name, sizeof(market[i].name), "%s", stock_id[i][0]);
    snprintf(market[i].symbol, sizeof(market[i].symbol), "%s", stock_id[i][1]);
    market[i].data = import_data(stock_id[i][1]);
    market[i].smooth_data = convolved_data(market[i].data);
  }
printf(" \n all data loaded...\n");
WAIT();

  deque_t * stock_ledger = deque_init();

  double funds = 5000.0;

  int day;
  for (day = 31; day < DATA_LEN - GK_RAD; day++) {
    funds = show_menu(market, day, stock_ledger, funds);
  }

  return 0;
}

void hline(int len, char ch) {
  int i;
  for (i = 0; i < len; i++) {
    printf("%c", ch);
  }
}

void hskip(int w) {
  int i;
  for (i = 0; i < w; i++) {
    printf(" ");
  }
}

void vskip(int h) {
  int i;
  for (i = 0; i < h; i++) {
    printf("\n");
  }
}

char * padr(char * str, unsigned int width) {
  char * new_str = malloc(sizeof(char) * (width + 1));
  unsigned int len = strlen(str);
  unsigned int i;
  for (i = 0; i < len; i++) {
    new_str[i] = str[i];
  }
  for (i = len; i < width; i++) {
    new_str[i] = ' ';
  }
  new_str[width] = '\0';
  return new_str;
}

double derivative(double * smooth_data, int day, int n) {
  if (n == 0) {
    return smooth_data[day];
  } else {
    double a = derivative(smooth_data, day - 1, n - 1);
    double b = derivative(smooth_data, day + 1, n - 1);
    return b - a;
  }
}


void purchase(int id, int shares, double price,
              deque_t * ledger, bool front,
              market_data_t * market) {
  ledger_entry_t * entry = malloc(sizeof(ledger_entry_t));
  entry->id = id;
  strcpy(entry->symbol, market[id].symbol);
  /* snprintf(entry->symbol, sizeof(entry->symbol), "%s", market[id].symbol); */
  entry->shares = shares;
  entry->purchase_price = price;
  printf("purchasing %d shares of %s at $%.2f\n",
         entry->shares,
         entry->symbol,
         entry->purchase_price);
  if (front) {
    deque_enqueuef(ledger, entry);
  } else {
    deque_enqueuer(ledger, entry);
  }
}

double show_menu(market_data_t * market, int day, deque_t * ledger,
                 double funds) {
  while (true) {
    vskip(24);
    hline(25, '=');
    printf("    day: %d", day - 31);
    vskip(1);
    printf("|  CURRENT MARKET DATA  |");
    printf("    ledger items: %d", deque_size(ledger));
    vskip(1);
    hline(25, '=');
    printf("    current funds: $%.2f", funds);
    printf("\n");
    hline(78, '-');
    printf("\n  ID  Symbol  Company\t\t Price\tChange\t  D(1)\t  D(2)\t Suggestion\n");
    hline(78, '-');
    printf("\n");
    int j;
    for (j = 0; j < MARKET_SIZE; j++) {
      double c = market[j].data[day] - market[j].data[day - 1];
      double d1 = derivative(market[j].data, day, 1);
      double d2 = derivative(market[j].data, day, 2);
      double w = tanh(0.05 * (0.25 * c + 0.75 * d1 + 0.25 * d2));
      char suggestion[BUFSIZ];
      if (w < -0.25) {
        strcpy(suggestion, C_RED"sell (");
      } else if (-0.25 <= w && w < 0.0) {
        strcpy(suggestion, C_YELLOW"hold (");
      } else if (0.0 <= w && w < 0.5) {
        strcpy(suggestion, C_RESET"hold (");
      } else {
        strcpy(suggestion, C_GREEN"buy  (");
      }

      /* char * suggestion = w < 0.0 ? "sell (" : "buy  ( "; */
      printf("   %d  %s  %s\t%6.2f\t%6.2f\t%6.2f\t%6.2f\t %s%4.3f)%s\n",
             j + 1,
             padr(market[j].symbol, 6),
             padr(market[j].name, 10),
             market[j].data[day],
             market[j].data[day] - market[j].data[day - 1],
             derivative(market[j].data, day, 1),
             derivative(market[j].data, day, 2),
             suggestion,
             w, C_RESET);
    }
    hline(78, '-');
    vskip(1);
    printf("  Ledger:\n");
    if (ledger->length == 0) {
      printf("    front: empty\t rear: empty\n");
      hline(78, '-');
      vskip(1);
      printf("  Menu:\n");
      int i;
      for (i = 0; i < MARKET_SIZE; i++) {
        printf("   %d) Buy shares of %s", i + 1, market[i].symbol);
        if (i % 3 == 2) printf("\n");
      }
      printf("   %d) Wait\n", i + 1);
      hline(78, '-');
      printf("\n  Select a number between 1 and %d: ", i + 1);
      int select = get_input_int(1, i + 1) - 1;
      if (select == i) {
        return funds;
      }
      double pp = market[select].data[day];
      int max_shares = (int)(funds / pp);
      if (max_shares > 0) {
        printf("  Enter the number of shares (max %d): ", max_shares);
        int shares = get_input_int(0, max_shares);
        printf("  Append to front (1) or rear (2) of ledger? ");
        bool fr = get_input_int(1, 2) == 1;
        purchase(select, shares, pp, ledger, fr, market);
        funds = funds - pp * shares;
      } else {
        printf("  You can't afford that\n");
        WAIT();
      }

    } else {
      ledger_entry_t * previewf = malloc(sizeof(ledger_entry_t));
      deque_peekf(ledger, previewf, sizeof(ledger_entry_t));
      unsigned int idf = previewf->id;
      char * symbolf = previewf->symbol;
      unsigned int sharesf = previewf->shares;
      double purchase_pricef = previewf->purchase_price;

      ledger_entry_t * previewr = malloc(sizeof(ledger_entry_t));
      deque_peekr(ledger, previewr, sizeof(ledger_entry_t));
      unsigned int idr = previewr->id;
      char * symbolr = previewr->symbol;
      unsigned int sharesr = previewr->shares;
      double purchase_pricer = previewr->purchase_price;

      printf("   front: %d shares of %s; purchased at $%.2f ($%.2f total)\n",
             sharesf, symbolf, purchase_pricef, purchase_pricef * sharesf);
      printf("   rear:  %d shares of %s; purchased at $%.2f ($%.2f total)\n",
             sharesr, symbolr, purchase_pricer, purchase_pricer * sharesr);

      hline(78, '-');
      vskip(1);
      printf("  Menu:\n");
      printf("   1) Buy   2) Sell   3) Wait\n");
      hline(78, '-');
      printf("\n  Select a number between 1 and 3: ");
      int buysell = get_input_int(1, 3);
      if (buysell == 3) {
        return funds;
      }
      int i;
      switch (buysell) {
        case 1:
          printf("  Purchase options:\n");
          for (i = 0; i < MARKET_SIZE; i++) {
            printf("   %d) %s", i + 1, market[i].symbol);
          }
          printf("\n  Select a number between 1 and %d: ", i);
          int select = get_input_int(1, i) - 1;
          double pp = market[select].data[day];
          int max_shares = (int)(funds / pp);
          if (max_shares > 0) {
            printf("  Enter the number of shares (max %d): ", max_shares);
            int shares = get_input_int(0, max_shares);
            printf("  Append to front (1) or rear (2) of ledger? ");
            bool fr = get_input_int(1, 2) == 1;
            purchase(select, shares, pp, ledger, fr, market);
            funds = funds - pp * shares;
          } else {
            printf("  You can't afford that\n");
            WAIT();
          }
          break;

        case 2:
          printf("  Selling options:\n");
          printf("   1) %s (front)   2) %s (rear)", symbolf, symbolr);
          printf("\n  Select a number between 1 and 2: ");
          int sel = get_input_int(1, 2);
          if (sel == 1) {
            printf("  How many (1 - %d)? ", sharesf);
            unsigned int sell_n = get_input_int(1, sharesf);
            deque_dequeuef(ledger, previewf, sizeof(ledger_entry_t));
            funds = funds + market[idf].data[day] * sell_n;
          } else {
            printf("  How many (1 - %d)? ", sharesr);
            int sell_n = get_input_int(1, sharesr);
            deque_dequeuer(ledger, previewr, sizeof(ledger_entry_t));
            funds = funds + market[idr].data[day] * sell_n;
          }
          if (deque_size(ledger) == 0) {
            ledger = deque_init();
          }
          break;

        default:
          break;
      }
      free(previewf);
      free(previewr);
    }
  }
  return funds;
}


double * convolved_data(double * data) {
  double * conv_kernel = gaussian_kernel(GK_RAD, GK_SIG);
  double * smooth_data = malloc(sizeof(double) * DATA_LEN);

  int i, j;
  for (i = 0; i < DATA_LEN; i++) {
    smooth_data[i] = data[i];
  }

  for (i = GK_RAD; i < DATA_LEN - GK_RAD; i++) {
    double sum = 0.0;
    for (j = -GK_RAD; j <= GK_RAD; j++) {
      sum += data[i + j] * conv_kernel[j + GK_RAD];
    }
    smooth_data[i] = sum;
  }
  return smooth_data;
}

double * trunc_gaussian_ker(size_t radius, double sig) {
  double * gk = gaussian_kernel(radius, sig);
  double * t_gk = malloc(sizeof(double) * radius + 1);
  double sum = 0.0;
  unsigned int i;
  for (i = 0; i < radius + 1; i++) {
    t_gk[i] = gk[i];
    sum += t_gk[i];
  }
  for (i = 0; i < GK_RAD + 1; i++) {
    t_gk[i] = t_gk[i] / sum;
  }
  return t_gk;
}

size_t write_f(void *ptr, size_t size, size_t nmemb, FILE *stream) {
    size_t written;
    written = fwrite(ptr, size, nmemb, stream);
    return written;
}

void download_data(char * symbol) {
  char * url_prefix = "http://real-chart.finance.yahoo.com/table.csv?s=";
  char * url_suffix = "&d=9&e=25&f=2014&g=d&a=2&b=27&c=2014&ignore=.csv";
  CURL * curl;
  FILE * file;
  CURLcode result;
  char url[URL_SIZE];
  char file_name[FILENAME_MAX];

  snprintf(url, URL_SIZE, "%s%s%s", url_prefix, symbol, url_suffix);
  snprintf(file_name, FILENAME_MAX, "%s.csv", symbol);
  printf(" retrieving URL:  %s\n", url);
  curl = curl_easy_init();
  if (curl) {
    file = fopen(file_name, "wb");
    curl_easy_setopt(curl, CURLOPT_URL, url);
    curl_easy_setopt(curl, CURLOPT_WRITEFUNCTION, write_f);
    curl_easy_setopt(curl, CURLOPT_WRITEDATA, file);
    result = curl_easy_perform(curl);
    if (result != 0) {
      printf("cURL error: %d\n", result);
      exit(EXIT_FAILURE);
    }
    curl_easy_cleanup(curl);
    fclose(file);
  }
}

double * import_data(char * symbol) {
  download_data(symbol);
  double * data = malloc(sizeof(double) * DATA_LEN);
  char fname[FILENAME_MAX];
  char buffer[BUFSIZ];
  snprintf(fname, FILENAME_MAX, "%s%s", symbol, ".csv");
  FILE * file = fopen(fname, "r");
  if (file == NULL) {
      perror("Error opening file");
      exit(EXIT_FAILURE);
  }
  fgets(buffer, BUFSIZ, file);  // skip the first line

  int i;
  for (i = 0; i < DATA_LEN; i++) {
    if (!fgets(buffer, BUFSIZ, file)) {
      perror("fgets");
      exit(EXIT_FAILURE);
    }
    char * tmp = strdup(buffer);
    double val = atof(getfield(tmp, 7));
    data[i] = val;
  }
  fclose(file);
  return data;
}

double _g(int x, double s) {
  double a = 1.0 / (sqrt(2.0 * PI) * s);
  double b = (double)(x * x) / (2.0 * s * s);
  return a * exp(-b);
}

double * gaussian_kernel(size_t radius, double sig) {
  double * kernel = malloc(sizeof(double) * (2 * radius + 1));
  unsigned int i;
  double sum;
  for (i = 0; i < 2 * radius + 1; i++) {
    kernel[i] = _g(i - radius, sig);
    sum += kernel[i];
  }
  for (i = 0; i < 2 * radius + 1; i++) {
    kernel[i] = kernel[i] / sum;
  }

  return kernel;
}

const char* getfield(char* line, int num) {
  const char* tok;
  for (tok = strtok(line, ",");
       tok && *tok;
       tok = strtok(NULL, ",\n")) {
    if (!--num)
      return tok;
  }
  return NULL;
}
