#!/bin/sh

#echo "arrival_air_prob, arrival_gnd_prob, time_duration, air_queue_size, gnd_queue_size, arrivals, departures" > data.csv

for i in `seq 1 8`;
do
	./collect_data.sh $i &
done
