#!/bin/bash

for i in `seq 1 8`;
do
    ./mandelbrot_ring 4096 -0.80050000054739 -0.17073749999872 4.0 50000 $i 129 1 8 /home/rhennigan/Pictures/mandelbrot &
done
