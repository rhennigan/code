#!/bin/bash

for i in `seq 100 100 5000`;
do
	count=0
	for j in `seq 1 100`;
	do
		res=$(`echo ./donuts $i 50 30 200`)
		count=`expr $count + $res`
	done
	echo $i", "$count
done
