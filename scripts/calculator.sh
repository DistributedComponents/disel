#!/usr/bin/env bash

if ! [ -x ./CalculatorMain.native ]
then
    echo 'CalculatorMain.native not found!'
    echo 'Run `make CalculatorMain.native` first.'
    exit 1
fi

(./CalculatorMain.native -me 1 -mode server 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 &) >server1.log 2>&1

(./CalculatorMain.native -me 3 -mode server 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 &) >server3.log 2>&1

./CalculatorMain.native -me 2 -mode client -server 3 1 127.0.0.1 9001 2 127.0.0.1 9002 3 127.0.0.1 9003 | tee client.log
