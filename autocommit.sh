#!/bin/sh

while true; do
	DATE=`date`
	echo " "
	echo "auto-commit changes: $DATE"
	echo " "
	git add -u
	git commit -m "auto-commit changes: $DATE"
	git push
	echo "waiting..."
	echo "________________________________________________________________________________"

	sleep 600
done
