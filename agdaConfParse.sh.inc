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
  echo "Everything.agda regenerated."
  echo
}
logFailed() {
  echo "Error: Running \`$1\` failed!"
}
logRunning() {
  echo "Generating Everything.agda by running \`$1\` in $(pwd):"
}
showCdIfNeeded() {
  myPath="$(dirname "$0")"
  if [ "${myPath}" != "." ]; then
    echo "$ cd ${myPath}"
  fi
}

generator=GenerateEverythingIlc
stackCmdName="stack exec --package ilc GenerateEverythingIlc"

if which "${generator}" > /dev/null; then
  logRunning "${generator}"
  ${generator} && { echo; logDone; } || { logFailed "${generator}"; exit 1; }
else
  echo "\`${generator}\` is not installed (consider running \`cabal install\` to fix that)."
  logRunning "$stackCmdName"
  echo

  eval $stackCmdName
  ret=$?
  echo
  if [ "$ret" -ne 0 ]; then
    logFailed "$stackCmdName"
    exit 1
  else
    logDone
  fi
fi

# vim: set ft=sh:
