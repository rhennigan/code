#! /bin/sh

# usage: A1_donut_loop.sh  number_of_runs_integer
# so from the shell prompt:  $ A1_donut_loop.sh 10 
# will run the proddonuts program and the consdonuts
# programs (5 of them) 10 times and report how many
# of the 10 runs ended in deadlock

if [ -z $1 ]
then
echo "USAGE: A1_donut_loop.sh  number_of_runs_integer number_of_consumers_integer"
echo "Try the command again"
echo " "
fi

echo " "
echo " "
echo " "
echo "The configuration is for $1 LOOPS and $2 CONSUMERS"
echo " "

local1=$1
lpcnt=1
count=0
while test $local1 -ne 0
do
echo "___________________________________________________________"
echo " "
echo "Working on LOOP $lpcnt"
echo " "
./proddonuts 50 > log/prod_out.txt & 
sleep 1 
for i in `seq 1 $2`;
do
  echo '\n\n----------------------------------------------------------' > log/c$i.txt
  echo '   CONSUMER '$i' ' >> log/c$i.txt
  echo '----------------------------------------------------------' >> log/c$i.txt
  ./consdonuts $i 50 10 >> log/c$i.txt &
done
#./consdonuts 1 >> c1 & ./consdonuts 2 >> c2 & ./consdonuts 3 >> c3 & ./consdonuts 4 >> c4 & ./consdonuts 5 >> c5 &
sleep 15
pid=`ps | grep -v 'grep' | grep 'proddonuts' | cut -c1-6`
if ps | grep -v 'grep' | grep -q 'consdonuts'
then
echo " "
echo "DEADLOCK DETECTED ON LOOP $lpcnt"
echo " "
count=`expr $count + 1`
else
echo "LOOP $lpcnt COMPLETED SUCCESSFULLY"
echo " "
fi
echo ">>>>>>>> NOW KILLING THE PRODUCER PROCESS PID: $pid"
kill $pid
local1=`expr $local1 - 1`
lpcnt=`expr $lpcnt + 1`
sleep 1
done
echo "___________________________________________________________"
echo " "
echo $1 loops and $count deadlocks
echo " "
echo " "
echo "CONSUMER OUTPUT"
for i in `seq 1 $2`;
do
  cat log/c$i.txt
done
