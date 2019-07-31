#!/bin/bash

cd $(dirname "$0")

if [[ "$1" == "-t" ]]; then
  TIMEOUT=$2
  shift 2
else
  TIMEOUT=60
fi

OPTS="-q $@"

function inf {
  time ./infsat $OPTS "$1" &
  PID=$!
  sleep $TIMEOUT && pkill -P $PID 2> /dev/null &
  WATCHER=$!
  wait $PID 2> /dev/null
  OUT=$?
  if [[ $OUT != 0 ]] && [[ $OUT != 1 ]] && [[ $OUT != 2 ]]; then
    echo -n real TIMEOUT 1>&2
  fi
  pkill -P $WATCHER
}

function bench {
  while read IN; do
    printf "%-40s" "${IN#benchmark/}"
    inf $IN 2>&1 > /dev/null | grep real | tail -n 1 | awk '{print $2}'
  done
}

echo "Benchmark of infsat $OPTS benchmark/* with timeout ${TIMEOUT}s"
echo "$(date +%Y-%m-%d) $(lscpu | sed -nr '/Model name/ s/.*:\s*(.*) @ .*/\1/p')"
echo --- input file ------------------------ time -----
find benchmark/ -name "*.inf" -type f | bench
