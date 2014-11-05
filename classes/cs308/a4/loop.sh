#!/bin/bash

for i in `seq 50 50 300`;
do
	count=0
	for j in `seq 1 100`;
	do
		res=$(`echo ./donuts $i 50 30 10`)
		count=`expr $count + $res`
	done
	echo $count
done
