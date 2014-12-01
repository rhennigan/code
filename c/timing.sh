#!/bin/bash

for j in `seq 1 1000000`;
do
	for i in `seq 1000000 1000000 10000000`;
	do
		output=$(./test $i | grep 'sort time' | sed 's/sort//g' | sed 's/time//g' | sed 's/= //g')
		echo $i, $output >> data$1.csv
	done
done
