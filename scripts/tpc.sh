#!/usr/bin/env bash

tpc=TPCMain.native

if ! [ -x ./$tpc ]
then
    echo "$tpc not found!"
    echo "Run 'make $tpc' first."
    exit 1
fi

(./$tpc -me 1 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >participant1.log

(./$tpc -me 2 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >participant2.log

(./$tpc -me 3 -mode participant 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 &) >participant3.log

./$tpc -me 0 -mode coordinator 0 127.0.0.1 8000 1 127.0.0.1 8001 2 127.0.0.1 8002 3 127.0.0.1 8003 | tee coordinator.log
