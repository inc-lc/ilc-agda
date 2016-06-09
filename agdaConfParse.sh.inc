# Emacs, this is -*- sh -*-

# Name of *the* file to check

mainFile=README.agda

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
