#!/bin/bash


# f=../../results/all062819 ; rm -rf $f; sh benchmark.sh 2>&1 | tee $f
FILES=../../tests/complexity/*.java
END=5
TIMEOUT=600   #10 mins
for f in $FILES
do
    for i in $(seq 1 $END); do
	echo "$i. analyzing $f"
	# take action on each file. $f store current file name
	timeout $TIMEOUT sage -python -O ../dig.py $f -log 3 -octmaxv 20 -seed $i 
    done
done
