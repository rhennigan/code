#!/bin/sh

n=0;

for x in `find -iname "*.c" -o -iname "*.h" -o -iname "Makefile" -type f`;
do
	c=`expr $(cat $x | wc -l)`
	n=`expr $n + $c`;
	echo $c':\t'$x
done

echo '\n'
echo '----------------'
echo 'total:\t'$n
