#!/bin/bash

cd "$(dirname "$0")"

. agdaConfParse.sh.inc

for i in $SRC; do
  /usr/bin/time -l agda -i . -i ${AGDA_LIB} $i
done
