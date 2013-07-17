#!/bin/bash
. agdaCheck.sh.conf
SRC="$(grep -E -v '^#|^$' agdaCheck.conf)"

for i in $SRC; do
  time agda -i . -i ${AGDA_LIB} $i
done
