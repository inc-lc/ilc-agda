#!/bin/bash

# CAUTION: This file should only be invoked in the directory it resides in!
#
#   ./agdaCheck.sh  # good
#
#   ../agdaCheck.sh # bad

# Load local configuration, which should not be committed to the repository.
# This is supposed to set AGDA_LIB.
. agdaCheck.sh.conf

# Load the list of files to check. This list should be committed to the
# repository; I chose the format hoping that it is parseable on Windows as well,
# but that's for Windows users (e.g. @Toxaris) to decide.

SRC="$(grep -E -v '^#|^$' agdaCheck.conf)"


if [ -z "${AGDA_LIB}" ]; then
  cat <<EOF
To setup this script, copy agdaCheck.sh.conf.example to agdaCheck.sh.conf and
edit it following the contained instructions. Please do not commit
agdaCheck.sh.conf to the repository, since its content is intrinsically local.
EOF
fi

for i in $SRC; do
  time agda -i . -i ${AGDA_LIB} $i
done
