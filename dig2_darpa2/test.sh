#!/bin/bash
for i in ./programs/hola/*.c
do
  echo $i
  filename=$(basename "$i")
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --maxdeg=4 &> eval-logs/$filename".log".1
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --maxdeg=4 &> eval-logs/$filename".log".2
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --maxdeg=4 &> eval-logs/$filename".log".3
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --maxdeg=4 &> eval-logs/$filename".log".4
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --maxdeg=4 &> eval-logs/$filename".log".5
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --noieqs --maxdeg=4 &> eval-logs/$filename".noieq.log".1
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --noieqs --maxdeg=4 &> eval-logs/$filename".noieq.log".2
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --noieqs --maxdeg=4 &> eval-logs/$filename".noieq.log".3
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --noieqs --maxdeg=4 &> eval-logs/$filename".noieq.log".4
  timeout -k 10s 10m $SAGE/sage --python dig2.py $i --noieqs --maxdeg=4 &> eval-logs/$filename".noieq.log".5
done 
