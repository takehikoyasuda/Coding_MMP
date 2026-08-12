#!/bin/sh
set -u

project_root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
failures=0

if ! command -v M2 >/dev/null 2>&1; then
    echo "ERROR: M2 was not found on PATH." >&2
    exit 127
fi

echo "Macaulay2 $(M2 --version)"

echo "== SteinFactorizationM2: standard suite =="
if ! (cd "$project_root/third_party/SteinFactorizationM2" && ./run-tests.sh); then
    failures=$((failures + 1))
fi

echo "== FlipComputation: package suite =="
if ! (cd "$project_root/third_party/flip-computation" && M2 --script tests/run-tests.m2); then
    failures=$((failures + 1))
fi

if [ "$failures" -ne 0 ]; then
    echo "ERROR: $failures upstream test suite(s) failed." >&2
    exit 1
fi

echo "All upstream test suites passed."
