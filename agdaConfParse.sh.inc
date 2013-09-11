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
fi

# Note for changers: using Markdown-style ` in output is convenient for readers,
# but troublesome for us since ` must be escaped, otherwise the shell will
# interpret `foo` as a request of running foo.
#
# Hence, ensure backticks are still quoted after modifying, and use $() if you
# actually want the escape behavior.

logDone() {
  echo "Everything.agda regenerated."
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

if which "${generator}" > /dev/null; then
  logRunning "${generator}"
  ${generator} && { echo; logDone; } || logFailed "${generator}"
else
  echo "\`${generator}\` is not installed (consider running \`cabal install\` to fix that)."
  logRunning "cabal run"
  echo

  cabal run
  ret=$?
  echo
  if [ "$ret" -ne 0 ]; then
    logFailed "cabal run"
    cat <<EOF
Most likely, either:
(1) some dependencies are missing, or
(2) your cabal release is older than 1.18 and does not support \`cabal run\`.
To fix missing dependencies (problem (1)), try running:

EOF
    showCdIfNeeded

    cat <<EOF
$ cabal install --only-dependencies -v --dry-run

and if the installation plan in cabal's output looks fine, run:

$ cabal install --only-dependencies
$ ./$(basename "$0")

If that fails, look at the output of cabal run to investigate the problem.

To workaround an old cabal (problem (2)), either update cabal or just run \`cabal install\` (similarly to the above instructions).
EOF
    exit 1
  else
    logDone
  fi
fi

# vim: set ft=sh:
