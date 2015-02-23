#!/bin/bash
SAVEIFS=$IFS
IFS=$(echo -en "\n\b")

if [ "$#" -eq 0 ]; then
	FILES=$(git status -s | sed 's/ M //g' | sed 's/A  //g' | sed 's/?? //g' | sed 's/\"//g')
else
	FILES=$(git status -s | sed 's/ M //g' | sed 's/A  //g' | sed 's/?? //g' | sed 's/\"//g' | grep $1)
fi

for file in $FILES
do
	echo 'ignoring: ' $file
	echo $file >> .gitignore
done

IFS=$SAVEIFS