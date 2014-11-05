#!/bin/bash

for i in `seq 100 5000 100`;
do
	count=0
	for j in `seq 1 100`;
	do
		res=$(`echo ./donuts $i 50 30 200`)
		echo $res
		count=`expr $count + $res`
	done
	echo $i", "$count
done
