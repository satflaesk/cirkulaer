#!/usr/bin/env bash

set -eoux pipefail;

cargo +nightly llvm-cov --branch --fail-uncovered-lines 0 --show-missing-lines "${@}";
