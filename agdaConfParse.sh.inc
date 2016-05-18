# Emacs, this is -*- sh -*-
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
  exit 1
fi

# Note for changers: using Markdown-style ` in output is convenient for readers,
# but troublesome for us since ` must be escaped, otherwise the shell will
# interpret `foo` as a request of running foo.
#
# Hence, ensure backticks are still quoted after modifying, and use $() if you
# actually want the escape behavior.

logDone() {
  echo
  echo "Everything.agda regenerated."
  echo
}
logFailed() {
  echo
  echo "Error: Running \`$1\` failed!"
}
logRunning() {
  echo "Generating Everything.agda by running \`$1\` in $(pwd):"
  echo
}

generator=GenerateEverythingIlc
stackCmdName="stack exec --package ilc $generator"

logRunning "$stackCmdName"
eval $stackCmdName && logDone || { logFailed "$stackCmdName"; exit 1; }

# vim: set ft=sh:
