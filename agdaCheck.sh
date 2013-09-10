#!/bin/bash

cd "$(dirname "$0")"

. agdaConfParse.sh.inc

/usr/bin/time -l agda -i . -i ${AGDA_LIB} ${mainFile}
