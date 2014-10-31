#!/bin/sh

#echo "arrival_air_prob, arrival_gnd_prob, time_duration, air_queue_size, gnd_queue_size, arrivals, departures" > data.csv

for i in `seq 0 30 300`;
do
	echo $1":" $(echo "scale = 2; 100 * $i / 300" | bc) "%"
	for j in `seq 0 30 300`;
	do
		aqt=0
		gqt=0
		ant=0
		gnt=0
		p1=0$(echo "scale = 3; $i / 1000" | bc)
		p2=0$(echo "scale = 3; $j / 1000" | bc)
		for k in `seq 1 500`;
		do
			row=$(./airport auto $p1 $p2 10 $k)
			aq=$(echo $row | sed s/' '/''/g | cut -f4 -d,)
			gq=$(echo $row | sed s/' '/''/g | cut -f5 -d,)
			an=$(echo $row | sed s/' '/''/g | cut -f6 -d,)
			gn=$(echo $row | sed s/' '/''/g | cut -f7 -d,)
			aqt=$(expr $aqt + $aq)
			gqt=$(expr $gqt + $gq)
			ant=$(expr $ant + $an)
			gnt=$(expr $gnt + $gn)
		done
		echo $p1 $p2 10 $aqt $gqt $ant $gnt >> data$1.csv
	done
done
