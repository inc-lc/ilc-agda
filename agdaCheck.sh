#!/bin/bash

cd "$(dirname "$0")"

. agdaConfParse.sh.inc

if [ -n "$agda_reproducible" ]; then
    prepend="stack exec --package Agda --"
else
    prepend=""
fi
$prepend agda +RTS -s -RTS -i . ${mainFile} "$@"
