#!/bin/bash

for k in `seq 1 1000`;
do
	for dz in `seq 100 50 300`;
	do
		for i in `seq 50 50 1000`;
		do
			count=0
			for j in `seq 1 100`;
			do
				res=$(`echo ./donuts $i 50 30 $dz`)
				count=`expr $count + $res`
			done
			echo $i", "$dz", "$count
			echo $i", "$dz", "$count >> "deadlocks.csv"
		done
	done
done
