#!/bin/bash

cd "$(dirname "$0")"

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

agda -i . -i ${AGDA_LIB} ${mainFile} --dependency-graph big.dot
filter-agda-dependency-graph < big.dot > small.dot
dot -Tpdf small.dot > small.pdf
