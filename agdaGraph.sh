#!/bin/bash

# CAUTION: This file should only be invoked in the directory it resides in!
#
#   ./agdaCheck.sh  # good
#
#   ../agdaCheck.sh # bad

. agdaConfParse.sh.inc

if ! which filter-agda-dependency-graph; then
  cat <<-EOF
	To run this script, install Tillmann's filter-agda-dependency-graph from
	Github, with something like:

	$ git clone https://github.com/Toxaris/filter-agda-dependency-graph.git
	$ cd filter-agda-dependency-graph
	$ cabal install -v --dry-run
	# Check that the installation plan makes sense, as usual with cabal
	# install.
	$ cabal install

	Exiting.
EOF
  exit 1
fi

for i in $SRC; do
  agda -i . -i ${AGDA_LIB} $i --dependency-graph big.dot
  filter-agda-dependency-graph < big.dot > small.dot
  dot -Tpdf small.dot > small.pdf
done
