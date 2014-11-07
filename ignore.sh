#!/bin/bash

echo $(git status -s | sed 's/?? //g') >> .gitignore
