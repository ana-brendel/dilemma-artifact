#!/bin/bash

if [ $1 == "group" || $1 == "group_updated"]; then
      python3 testing_scripts/run.py $1 $2
    else
      python3 testing_scripts/run.py $1
    fi
