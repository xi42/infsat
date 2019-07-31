#!/bin/bash

cd $(dirname "$0")

OPTS="-q $@"

TIMEOUT=60

function inf {
  time ./infsat -q $OPTS "$1" &
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
find benchmark/ -type f | bench
