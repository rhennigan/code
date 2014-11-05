#!/bin/bash

for i in `seq 50 50 500`;
do
	count=0
	for j in `seq 1 100`;
	do
		res=$(`echo ./donuts $i 50 30 10`)
		count=`expr $count + $res`
	done
	echo $i", "$count
done
