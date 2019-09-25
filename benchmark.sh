#!/bin/bash

cd $(dirname "$0")

if [[ "$1" == "-d" ]]; then
  DIR="$2"
  shift 2
else
  DIR=benchmark
fi

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
    echo "real TIMEOUT" 1>&2
  fi
  echo "code $OUT" 1>&2
  pkill -P $WATCHER
}

function bench {
  while read IN; do
    OUT=($(inf $IN 2>&1 > /dev/null | grep "real\|code" | tail -n 2 | sort | awk '{print $2}'))
    TIME="${OUT[1]}"
    if [[ ${OUT[0]} == 0 ]]; then
      RESULT="INF"
    elif [[ ${OUT[0]} == 1 ]]; then
      RESULT="FIN (UNSAFE)"
    elif [[ ${OUT[0]} == 42 ]]; then
      RESULT="FIN"
    elif [[ ${OUT[0]} == 143 ]]; then
      RESULT="SIGTERM"
    else
      RESULT="ERROR"
    fi
    printf "%-40s %-15s %s\n" "${IN#benchmark/}" "${TIME}" "$RESULT"
  done
}

echo "Benchmark of infsat $OPTS benchmark/* with timeout ${TIMEOUT}s"
echo "$(date +%Y-%m-%d) $(lscpu | sed -nr '/Model name/ s/.*:\s*(.*) @ .*/\1/p')"
echo "--- input file ------------------------- time ---------- result ---"
find "$DIR/" -name "*.inf" -type f | sort | bench
