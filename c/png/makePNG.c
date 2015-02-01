// LibPNG example
// A.Greensted
// http://www.labbookpages.co.uk

// Version 2.0
// With some minor corrections to Mandlebrot code (thanks to Jan-Oliver)

// Version 1.0 - Initial release
#include <omp.h>
#include <stdio.h>
#include <stdlib.h>
#include <math.h>
#include <malloc.h>
#include <png.h>



// Creates a test image for saving. Creates a Mandelbrot Set fractal of size width x height
double *createMandelbrotImage(int width, int height, double xS, double yS, double rad, int maxIteration);

double *createQuasicrystalImage(int width, int height, int order, double phase, double scale, double mag, double dX, double dY);

// This takes the double value 'val', converts it to red, green & blue values, then 
// sets those values into the image memory buffer location pointed to by 'ptr'
inline void setRGB(png_byte *ptr, double val);

// This function actually writes out the PNG image file. The string 'title' is
// also written into the image file
int writeImage(char* filename, int width, int height, double *buffer, char* title);

double minVal = 1.0;
double maxVal = 0.0;
double minValOld = 1.0;
double maxValOld = 0.0;

int main(int argc, char *argv[])
{
	// Make sure that the output filename argument has been provided
	/* if (argc != 2) { */
	/* 	fprintf(stderr, "Please specify output file\n"); */
	/* 	return 1; */
	/* } */

	// Specify an output image size
	int width = atoi(argv[1]);
	int height = atoi(argv[2]);
  double dX = atof(argv[3]); // -0.802
  double dY = atof(argv[4]); // -0.177
  double rad = atof(argv[5]); // 0.011
  int iter = atoi(argv[6]);
  int start = atoi(argv[7]);
  int end = atoi(argv[8]);
  int skip = atoi(argv[9]);
  int cores = atoi(argv[10]);

  double scale = (double)(width - 8) / (double)(width);

  rad = 1.5;
	// Create a test image - in this case a Mandelbrot Set fractal
	// The output is a 1D array of doubles, length: width * height

  
  int n;
  for (n = start; n < end; n+=cores*skip) {
    /* rad = rad * 0.99; */
    printf("Creating Image (%d, %d, %f, %f, %.16f, %d)\n", width, height, dX, dY, rad * pow(scale, (double)n), iter);
    minValOld = minVal;
    maxValOld = maxVal;
    minVal = 1.0;
    maxVal = 0.0;
    double *buffer = createMandelbrotImage(width, height, dX, dY, rad * pow(scale, (double)n), iter);
    printf("minVal: %f, %f\n", minVal, minValOld);
    printf("maxVal: %f, %f\n", maxVal, maxValOld);
    maxVal = 0.1 * maxVal + 0.9 * maxValOld;
    minVal = 0.1 * minVal + 0.9 * minValOld;
    printf("new minVal: %f, %f\n", minVal, minValOld);
    printf("new maxVal: %f, %f\n", maxVal, maxValOld);
    double range = maxVal - minVal;
    int i;
    for (i = 0; i < width * height; i++) {
      buffer[i] = (buffer[i] - minVal) / range;
    }

    /* printf("\n\n\n\n"); */
    /* double *buffer2 = createQuasicrystalImage(width, height, 5, 0.0, 0.1, 0.5, 0.0, 0.0); */
    if (buffer == NULL) {
      return 1;
    }

    // Save the image to a PNG file
    // The 'title' string is stored as part of the PNG file
    printf("Saving PNG\n");
    char file[255];
    sprintf(file, "frames/mandelbrot_%d.png", n);
    writeImage(file, width, height, buffer, "This is my test image");
    /* int result2 = writeImage(argv[1], width, height, buffer2, "This is my test image"); */
  
    // Free up the memorty used to store the image
    free(buffer);
    /* free(buffer2); */
  }
	return 0;
}

#define SNAP(x) ((x) < 0 ? 0 : (x) > 255 ? 255 : (x))

inline void setRGB(png_byte *ptr, double val)
{
  int r = SNAP((int)(sqrt(val) * 255));
  int g = SNAP((int)(val * 255));
  int b = SNAP((int)(val * val * 255));
  ptr[0] = r; ptr[1] = g; ptr[2] = b;
}

/* inline void setRGB(png_byte *ptr, double val) */
/* { */
/* 	int v = (int)(val * 767); */
/* 	if (v < 0) v = 0; */
/* 	if (v > 767) v = 767; */
/* 	int offset = v % 256; */

/* 	if (v<256) { */
/* 		ptr[0] = 0; ptr[1] = 0; ptr[2] = offset; */
/* 	} */
/* 	else if (v<512) { */
/* 		ptr[0] = 0; ptr[1] = offset; ptr[2] = 255-offset; */
/* 	} */
/* 	else { */
/* 		ptr[0] = offset; ptr[1] = 255-offset; ptr[2] = 0; */
/* 	} */
/* } */

int writeImage(char* filename, int width, int height, double *buffer, char* title)
{
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
		for (x=0 ; x<width ; x++) {
			setRGB(&(row[x*3]), buffer[y*width + x]);
		}
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

double *createMandelbrotImage(int width, int height, double xS, double yS, double rad, int maxIteration)
{
	double *buffer = (double *) malloc(width * height * sizeof(double));
	if (buffer == NULL) {
		fprintf(stderr, "Could not create image buffer\n");
		return NULL;
	}

	// Create Mandelbrot set image

	int xPos, yPos;
	double minMu = maxIteration;
	double maxMu = 0;

 
	for (yPos=0 ; yPos<height ; yPos++)
	{
		double yP = (yS-rad) + (2.0f*rad/height)*yPos;

		for (xPos=0 ; xPos<width ; xPos++)
		{
			double xP = (xS-rad) + (2.0f*rad/width)*xPos;

			int iteration = 0;
			double x = 0;
			double y = 0;

			while (x*x + y*y <= 4 && iteration < maxIteration)
			{
				double tmp = x*x - y*y + xP;
				y = 2*x*y + yP;
				x = tmp;
				iteration++;
			}

			if (iteration < maxIteration) {
				double modZ = sqrt(x*x + y*y);
				/* double mu = iteration - (log(log(modZ))) / log(2); */
        double mu = iteration - modZ;
				if (mu > maxMu) maxMu = mu;
				if (mu < minMu) minMu = mu;
				buffer[yPos * width + xPos] = mu;
			}
			else {
				buffer[yPos * width + xPos] = 0;
			}
		}
	}

	// Scale buffer values between 0 and 1
	int count = width * height;
	while (count) {
		count --;
		buffer[count] = (buffer[count] - minMu) / (maxMu - minMu);
    minVal = buffer[count] < minVal ? buffer[count] : minVal;
    maxVal = buffer[count] > maxVal ? buffer[count] : maxVal;
	}

	return buffer;
}

double *createQuasicrystalImage(int width, int height, int order, double phase, double scale, double mag, double dX, double dY) {
  double *buffer = (double *) malloc(width * height * sizeof(double));
	if (buffer == NULL) {
		fprintf(stderr, "Could not create image buffer\n");
		return NULL;
	}

  int xIndex, yIndex;
  
  for (yIndex = 0; yIndex < height; yIndex++) {
    for (xIndex = 0; xIndex < width; xIndex++) {
      int index = height*yIndex + xIndex;
      double x = ((double)xIndex + dX - (double)width  / 2.0f);
      double y = ((double)yIndex + dY - (double)height / 2.0f);
      double d = (double)order;
      double sum = 0.0f;

      double k;
      for(k = 0.0f; k < d; k += 1.0f) {
        sum = sum + cos(scale * x * cos(k * 3.14159f / d) - scale * y * sin(k * 3.14159f / d) + phase);
      }
	
      sum = mag * sum;

      int s = (int)sum;
      if (s % 2 == 1) {
        sum = 1.0f - fmod(sum, 1.0f);
      }
      else {
        sum = fmod(sum, 1.0f);
      }

      sum = 0.5*(sum+1.0);
      buffer[index] = sum;
    }
  }
  return buffer;
}
