#!/bin/bash

for i in `seq 1 8`;
do
		./mandelbrot_ring 2048 -0.80050000054739 -0.17073749999872 4.0 50000 $i 129 1 8 /media/rhennigan/00F28D34F28D2F4A/mandelbrot &
done
