# Load local configuration, which should not be committed to the repository.
# This is supposed to set AGDA_LIB.
. agdaCheck.sh.conf

# Name of *the* file to check

mainFile=README.agda

if [ -z "${AGDA_LIB}" ]; then
  cat <<EOF
To setup this script, copy agdaCheck.sh.conf.example to agdaCheck.sh.conf and
edit it following the contained instructions. Please do not commit
agdaCheck.sh.conf to the repository, since its content is intrinsically local.
EOF
fi

# vim: set ft=sh:
