#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <malloc.h>

int * mandelbrot_ring(int s, double xs, double ys, double rad, int iter);
double * mandelbrot_end(int s, double xs, double ys, double r, int it);
void  write_data(char * file, int size, double * buffer);

int main(int argc, char *argv[]) {
	int size = atoi(argv[1]);
  double dX = atof(argv[2]); // -0.802
  double dY = atof(argv[3]); // -0.177
  double rad = atof(argv[4]); // 0.011 (2.0)
  int iter = atoi(argv[5]);
  int start = atoi(argv[6]);
  int end = atoi(argv[7]);
  int skip = atoi(argv[8]);
  int cores = atoi(argv[9]);
  char * path = argv[10];

  double scale = 0.5;

  int n;
  for (n = start*skip; n < end; n+=cores*skip) {
    printf("creating buffer (%d, %f, %f, %.16f, %d)\n", size, dX, dY, rad * pow(scale, (double)n), iter);
    double * buffer = mandelbrot_end(size, dX, dY, rad * pow(scale, (double)n), iter);
    if (buffer == NULL) exit(EXIT_FAILURE);

    printf("writing file %d\n", n);
    char file[255];
    sprintf(file, "%s/mandelbrot_%d.csv", path, n);
    write_data(file, size*size, buffer);
    free(buffer);
  }
  
	return 0;
}

void write_data(char * file, int size, double * buffer) {
  FILE * fp = fopen(file, "w");
  int i;
  for (i = 0; i < size; i++) 
    fprintf(fp, "%f\n", buffer[i]);
  fclose(fp);
}

int * mandelbrot_ring(int s, double xs, double ys, double r, int it) {
	int * buffer = (int *) malloc(4 * s * sizeof(int));
	if (buffer == NULL) {
		fprintf(stderr, "out of memory\n");
		return NULL;
	}

	int xPos, yPos;
  double yP, xP;

  yPos = 0;
  yP = (ys-r) + (2.0f*r/s)*yPos;
  for (xPos = 0; xPos < s; xPos++) {
    xP = (xs-r) + (2.0f*r/s)*xPos;
    int iteration = 1;
    double x = 0;
    double y = 0;
    while (x*x + y*y <= 4 && iteration < it) {
      double tmp = x*x - y*y + xP;
      y = 2*x*y + yP;
      x = tmp;
      iteration++;
    }
    buffer[xPos] = iteration < it ? iteration : 0;
  }

  yPos = s - 1;
  yP = (ys-r) + (2.0f*r/s)*yPos;
  for (xPos = 0; xPos < s; xPos++) {
    xP = (xs-r) + (2.0f*r/s)*xPos;
    int iteration = 1;
    double x = 0;
    double y = 0;
    while (x*x + y*y <= 4 && iteration < it) {
      double tmp = x*x - y*y + xP;
      y = 2*x*y + yP;
      x = tmp;
      iteration++;
    }
    buffer[s + xPos] = iteration < it ? iteration : 0;
  }

  xPos = 0;
  xP = (xs-r) + (2.0f*r/s)*xPos;
  for (yPos = 0; yPos < s; yPos++) {
    yP = (ys-r) + (2.0f*r/s)*yPos;
    int iteration = 1;
    double x = 0;
    double y = 0;
    while (x*x + y*y <= 4 && iteration < it) {
      double tmp = x*x - y*y + xP;
      y = 2*x*y + yP;
      x = tmp;
      iteration++;
    }
    buffer[2*s + yPos] = iteration < it ? iteration : 0;
  }

  xPos = s - 1;
  xP = (xs-r) + (2.0f*r/s)*xPos;
  for (yPos = 0; yPos < s; yPos++) {
    yP = (ys-r) + (2.0f*r/s)*yPos;
    int iteration = 1;
    double x = 0;
    double y = 0;
    while (x*x + y*y <= 4 && iteration < it) {
      double tmp = x*x - y*y + xP;
      y = 2*x*y + yP;
      x = tmp;
      iteration++;
    }
    buffer[3*s + yPos] = iteration < it ? iteration : 0;
  }

	return buffer;
}

double * mandelbrot_end(int s, double xs, double ys, double r, int it) {
	double * buffer = (double *) malloc(s * s * sizeof(double));
	if (buffer == NULL) {
		fprintf(stderr, "out of memory\n");
		return NULL;
	}

	int xPos, yPos;

  for (yPos = 0; yPos < s; yPos++) {
    double yP = (ys-r) + (2.0f*r/s)*yPos;
    for (xPos = 0; xPos < s; xPos++) {
      double xP = (xs-r) + (2.0f*r/s)*xPos;
      int iteration = 1;
      double x = 0;
      double y = 0;
      while (x*x + y*y <= 4 && iteration < it) {
        double tmp = x*x - y*y + xP;
        y = 2*x*y + yP;
        x = tmp;
        iteration++;
      }
      buffer[yPos * s + xPos] = iteration < it ? iteration - (log(log(sqrt(x*x + y*y)))) / log(2) : 0;
    }
  }

	return buffer;
}
