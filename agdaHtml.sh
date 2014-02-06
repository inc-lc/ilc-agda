#!/bin/bash

cd "$(dirname "$0")"

. agdaConfParse.sh.inc

agda -i . -i ${AGDA_LIB} ${mainFile} --html
