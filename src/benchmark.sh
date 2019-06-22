#!/bin/bash
FILES=../tests/nla/*.java
END=1
for f in $FILES
do
    for i in $(seq 1 $END); do
	echo "$i. Processing $f file..."
	# take action on each file. $f store current file name
	sage -python -O dig.py $f -log 3 -octmaxv 20 -seed $i
     done
done
