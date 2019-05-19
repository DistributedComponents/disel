#!/usr/bin/env bash

calculator=CalculatorMain.native

if ! [ -x ./$calculator ]
then
    echo "$calculator not found!"
    echo "Run 'make $calculator' first."
    exit 1
fi

(./$calculator -me 1 -mode server 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 &) >server1.log 2>&1

(./$calculator -me 3 -mode server 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 &) >server3.log 2>&1

./$calculator -me 2 -mode client -server 3 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 | tee client.log
