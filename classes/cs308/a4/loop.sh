#!/bin/bash

for k in `seq 1 100`;
do
	for i in `seq 250 50 750`;
	do
		count=0
		for j in `seq 1 100`;
		do
			res=$(`echo ./donuts $i 50 30 200`)
			count=`expr $count + $res`
		done
		echo $i", "$count
		echo $i", "$count >> "deadlocks.csv"
	done
done
