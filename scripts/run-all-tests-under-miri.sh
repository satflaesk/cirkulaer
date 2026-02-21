#!/usr/bin/env bash

set -eoux pipefail;

cargo +nightly miri test "${@}";
