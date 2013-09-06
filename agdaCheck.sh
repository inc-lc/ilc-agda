#!/bin/bash

# CAUTION: This file should only be invoked in the directory it resides in!
#
#   ./agdaCheck.sh  # good
#
#   ../agdaCheck.sh # bad

. agdaConfParse.sh.inc

for i in $SRC; do
  /usr/bin/time -l agda -i . -i ${AGDA_LIB} $i
done
