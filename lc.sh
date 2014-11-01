#!/bin/bash

n=0;
i=0;
lst=();

for x in `find -iname "*.c" -o -iname "*.h" -o -iname "Makefile" -type f`;
do
	c=`expr $(cat $x | wc -l)`
	n=`expr $n + $c`;
	lst+=($(echo -e $c"\t"$x))
done

printf "%s %s\n" "${lst[@]}" | sort -g | sed 's/\.\///g'

echo '----------------'
echo 'total: '$n
