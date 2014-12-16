#!/bin/bash

git status -s | grep '??' | sed 's/?? //g' >> .gitignore
