#!/bin/bash

git status -s | grep '?? ' | sed 's/?? //g' | sed 's/\#/\\#/g' >> .gitignore
