#!/bin/sh
# Capture a real Macaulay2 session transcript for each worked example.
#
# The scripts are fed on standard input rather than given as a file argument,
# so that Macaulay2 echoes them the way it echoes an interactive session: the
# .out files are then genuine transcripts, not reformatted output.  printWidth
# is set with -e so that it does not appear in the transcript itself.
#
# Each run also records its wall time, in seconds, in a .time file beside the
# transcript; the published page quotes those.
#
# Usage: examples/run.sh [example.m2 ...]   (default: all of them)
# Must be run from the repository root, since the examples load
# MMPComputation.m2 by path.
set -eu
cd "$(dirname "$0")/.."
[ $# -gt 0 ] && set -- "$@" || set -- examples/*.m2
for f in "$@"; do
  out="${f%.m2}.out"
  echo "=== $f -> $out"
  start=$(date +%s)
  M2 --no-readline -q -e 'printWidth = 74' < "$f" > "$out.raw" 2>&1
  end=$(date +%s)
  # Drop Macaulay2's two-line banner, the blank line after it, and the
  # unanswered prompt Macaulay2 prints when standard input reaches EOF.
  sed -e '1,3d' "$out.raw" | sed -e '$ d' > "$out"
  rm -f "$out.raw"
  echo "$((end - start))" > "${f%.m2}.time"
  echo "    $((end - start))s"
done
