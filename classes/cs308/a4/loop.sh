#!/bin/bash

for i in `seq 10 50 10`;
do
	count=0
	for j in `seq 1 1000`;
	do
		res=$(`echo ./donuts $i 50 30 200`)
		echo $res
		count=`expr $count + $res`
	done
	echo $i", "$count
done
