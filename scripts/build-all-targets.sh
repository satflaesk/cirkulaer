#!/usr/bin/env bash

set -eoux pipefail;

cargo build --all-targets "${@}";
