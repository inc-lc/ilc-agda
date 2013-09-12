#!/bin/bash

cd "$(dirname "$0")"

. agdaConfParse.sh.inc

agda +RTS -s -RTS -i . -i ${AGDA_LIB} ${mainFile}
