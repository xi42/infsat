#!/bin/bash

TIMEOUT=600

./benchmark.sh -t $TIMEOUT | tee benchmark/benchmark-`date '+%Y-%m-%d'`.txt
./benchmark.sh -t $TIMEOUT -nofntty| tee benchmark/benchmark-`date '+%Y-%m-%d'`-nofntty.txt
./benchmark.sh -t $TIMEOUT -noftty | tee benchmark/benchmark-`date '+%Y-%m-%d'`-noftty.txt
./benchmark.sh -t $TIMEOUT -noftty -nofntty | tee benchmark/benchmark-`date '+%Y-%m-%d'`-noftty-nofntty.txt
./benchmark.sh -t $TIMEOUT -nohvo | tee benchmark/benchmark-`date '+%Y-%m-%d'`-nohvo.txt
./benchmark.sh -t $TIMEOUT -nohvo -nofntty | tee benchmark/benchmark-`date '+%Y-%m-%d'`-nohvo-nofntty.txt
./benchmark.sh -t $TIMEOUT -nohvo -noftty | tee benchmark/benchmark-`date '+%Y-%m-%d'`-nohvo-noftty.txt
./benchmark.sh -t $TIMEOUT -nohvo -noftty -nofntty | tee benchmark/benchmark-`date '+%Y-%m-%d'`-nohvo-noftty-nofntty.txt
