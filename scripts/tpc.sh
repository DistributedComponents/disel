#!/usr/bin/env bash

if ! [ -x ./TPCMain.native ]
then
    echo 'TPCMain.native not found!'
    echo 'Run `make TPCMain.native` first.'
    exit 1
fi

(./TPCMain.native -me 1 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >participant1.log

(./TPCMain.native -me 2 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >participant2.log

(./TPCMain.native -me 3 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >participant3.log

./TPCMain.native -me 0 -mode coordinator 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 | tee coordinator.log
