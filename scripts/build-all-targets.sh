#!/usr/bin/env bash

set -eoux pipefail;

RUSTFLAGS="-D warnings" cargo build --all-targets "${@}";
