#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <malloc.h>
#include <png.h>

double * mandelbrot_vals(int w, int h, double xs, double ys, double rad, int iter);
int * mandelbrot_ring(int s, double xs, double ys, double rad, int iter);

inline void color_px(png_byte *ptr, double val);

int save_png(char* filename, int width, int height, double *buffer, char* title);

double minVal = 0.0;
double maxVal = 1.0;
double minValOld = 0.0;
double maxValOld = 1.0;
double p = 0.1;
double scale = 0.9816070644969339120677887;

int main(int argc, char *argv[]) {
	int width = atoi(argv[1]);
	int height = atoi(argv[2]);
  double dX = atof(argv[3]); // -0.802
  double dY = atof(argv[4]); // -0.177
  double rad = atof(argv[5]); // 0.011 (2.0)
  int iter = atoi(argv[6]);
  int start = atoi(argv[7]);
  int end = atoi(argv[8]);
  int skip = atoi(argv[9]);
  int cores = atoi(argv[10]);

  int n;
  for (n = start*skip; n < end; n+=cores*skip) {
    printf("creating buffer (%d, %d, %f, %f, %.16f, %d)\n", width, height, dX, dY, rad * pow(scale, (double)n), iter);
    double *buffer = mandelbrot_vals(width, height, dX, dY, rad * pow(scale, (double)n), iter);
    if (buffer == NULL) exit(EXIT_FAILURE);

    minValOld = minVal;
    maxValOld = maxVal;
    minVal = 1.0;
    maxVal = 0.0;
    
    printf("minVal: %f, %f\n", minVal, minValOld);
    printf("maxVal: %f, %f\n", maxVal, maxValOld);
    maxVal = p * maxVal + (1.0 - p) * maxValOld;
    minVal = p * minVal + (1.0 - p) * minValOld;
    printf("new minVal: %f, %f\n", minVal, minValOld);
    printf("new maxVal: %f, %f\n", maxVal, maxValOld);
    double range = maxVal - minVal;
    
    int i;
    for (i = 0; i < width * height; i++) 
      buffer[i] = (buffer[i] - minVal) / range;

    printf("writing file %d\n", n);
    char file[255];
    sprintf(file, "frames/mandelbrot_%d.png", n);
    save_png(file, width, height, buffer, "mandelbrot");
    free(buffer);
  }
	return 0;
}

#define SNAP(x) ((x) < 0 ? 0 : (x) > 255 ? 255 : (x))
#define S(x, a, b) ((x) < (a) ? (a) : (x) > (b) ? (b) : (x))
#define INT(x, a, b) (((x) - (a)) / ((b) - (a)))

const int c1[3] = {215, 224, 229};
const int c2[3] = { 12,  90, 129};
const int c3[3] = {  0,   0,   0};
const int c4[3] = {214,  74,  39};
const int c5[3] = {255, 255, 255};
const double p1 = 0.25;
const double p2 = 0.50;
const double p3 = 0.75;

inline void color_px(png_byte *ptr, double val) {
  double v = S(val, 0.0, 1.0);
  if (v <= -0.00001) {
    ptr[0] = 0;
    ptr[1] = 0;
    ptr[2] = 0;
  } else if (v < p1) {
    double t2 = INT(v, 0.0, p1);
    double t1 = 1.0 - t2;
    ptr[0] = (int)(t1 * c1[0] + t2 * c2[0]);
    ptr[1] = (int)(t1 * c1[1] + t2 * c2[1]);
    ptr[2] = (int)(t1 * c1[2] + t2 * c2[2]);
  } else if (v < p2) {
    double t2 = INT(v, p1, p2);
    double t1 = 1.0 - t2;
    ptr[0] = (int)(t1 * c2[0] + t2 * c3[0]);
    ptr[1] = (int)(t1 * c2[1] + t2 * c3[1]);
    ptr[2] = (int)(t1 * c2[2] + t2 * c3[2]);
  } else if (v < p3) {
    double t2 = INT(v, p2, p3);
    double t1 = 1.0 - t2;
    ptr[0] = (int)(t1 * c3[0] + t2 * c4[0]);
    ptr[1] = (int)(t1 * c3[1] + t2 * c4[1]);
    ptr[2] = (int)(t1 * c3[2] + t2 * c4[2]);
  } else {
    double t2 = INT(v, p3, 1.0);
    double t1 = 1.0 - t2;
    ptr[0] = (int)(t1 * c4[0] + t2 * c5[0]);
    ptr[1] = (int)(t1 * c4[1] + t2 * c5[1]);
    ptr[2] = (int)(t1 * c4[2] + t2 * c5[2]);
  }
}

int save_png(char * filename, int width, int height, double *buffer, char* title) {
	int code = 0;
	FILE *fp;
	png_structp png_ptr;
	png_infop info_ptr;
	png_bytep row;
	
	// Open file for writing (binary mode)
	fp = fopen(filename, "wb");
	if (fp == NULL) {
		fprintf(stderr, "Could not open file %s for writing\n", filename);
		code = 1;
		goto finalise;
	}

	// Initialize write structure
	png_ptr = png_create_write_struct(PNG_LIBPNG_VER_STRING, NULL, NULL, NULL);
	if (png_ptr == NULL) {
		fprintf(stderr, "Could not allocate write struct\n");
		code = 1;
		goto finalise;
	}

	// Initialize info structure
	info_ptr = png_create_info_struct(png_ptr);
	if (info_ptr == NULL) {
		fprintf(stderr, "Could not allocate info struct\n");
		code = 1;
		goto finalise;
	}

	// Setup Exception handling
	if (setjmp(png_jmpbuf(png_ptr))) {
		fprintf(stderr, "Error during png creation\n");
		code = 1;
		goto finalise;
	}

	png_init_io(png_ptr, fp);

	// Write header (8 bit colour depth)
	png_set_IHDR(png_ptr, info_ptr, width, height,
               8, PNG_COLOR_TYPE_RGB, PNG_INTERLACE_NONE,
               PNG_COMPRESSION_TYPE_BASE, PNG_FILTER_TYPE_BASE);

	// Set title
	if (title != NULL) {
		png_text title_text;
		title_text.compression = PNG_TEXT_COMPRESSION_NONE;
		title_text.key = "Title";
		title_text.text = title;
		png_set_text(png_ptr, info_ptr, &title_text, 1);
	}

	png_write_info(png_ptr, info_ptr);

	// Allocate memory for one row (3 bytes per pixel - RGB)
	row = (png_bytep) malloc(3 * width * sizeof(png_byte));

	// Write image data
	int x, y;
	for (y=0 ; y<height ; y++) {
		for (x=0 ; x<width ; x++) 
			color_px(&(row[x*3]), buffer[y*width + x]);
		png_write_row(png_ptr, row);
	}

 	// End write
	png_write_end(png_ptr, NULL);

finalise:
	if (fp != NULL) fclose(fp);
	if (info_ptr != NULL) png_free_data(png_ptr, info_ptr, PNG_FREE_ALL, -1);
	if (png_ptr != NULL) png_destroy_write_struct(&png_ptr, (png_infopp)NULL);
	if (row != NULL) free(row);

	return code;
}

double * mandelbrot_vals(int w, int h, double xs, double ys, double r, int it) {
	double *buffer = (double *) malloc(w * h * sizeof(double));
	if (buffer == NULL) {
		fprintf(stderr, "out of memory\n");
		return NULL;
	}

	int xPos, yPos;
	double minMu = it;
	double maxMu = 0;

 
	for (yPos = 0; yPos < h; yPos++) {
		double yP = (ys-r) + (2.0f*r/h)*yPos;

		for (xPos = 0; xPos < w; xPos++) {
			double xP = (xs-r) + (2.0f*r/w)*xPos;

			int iteration = 0;
			double x = 0;
			double y = 0;

			while (x*x + y*y <= 4 && iteration < it) {
				double tmp = x*x - y*y + xP;
				y = 2*x*y + yP;
				x = tmp;
				iteration++;
			}

			if (iteration < it) {
				double modZ = sqrt(x*x + y*y);
				double mu = log(3.0 + iteration - (log(log(modZ))) / log(2));
				if (mu > maxMu) maxMu = mu;
				if (mu < minMu) minMu = mu;
				buffer[yPos * w + xPos] = mu;
			} else {
				buffer[yPos * w + xPos] = 0;
			}
		}
	}

	int count = w * h;
	while (count) {
		count --;
		buffer[count] = (buffer[count] - minMu) / (maxMu - minMu);
    minVal = buffer[count] != 0.0 && buffer[count] < minVal ? buffer[count] : minVal;
    maxVal = buffer[count] > maxVal ? buffer[count] : maxVal;
	}

	return buffer;
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
    buffer[2*s + yPos] = iteration < it ? iteration : 0;
  }

	return buffer;
}
