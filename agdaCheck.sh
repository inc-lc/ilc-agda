#!/bin/bash

cd "$(dirname "$0")"

. agdaConfParse.sh.inc

stack exec --package Agda -- agda +RTS -s -RTS -i . ${mainFile} "$@"
