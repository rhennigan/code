#!/bin/bash
SAVEIFS=$IFS
IFS=$(echo -en "\n\b")
FILES=$(git status -s | sed 's/ M //g' | sed 's/A  //g' | sed 's/?? //g' | sed 's/\"//g' | grep $1)

for file in $FILES
do
	echo $file >> .gitignore
done

IFS=$SAVEIFS