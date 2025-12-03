#!/usr/bin/env bash

set -eoux pipefail;

cargo llvm-cov --branch --fail-uncovered-lines 0 --show-missing-lines "${@}";
