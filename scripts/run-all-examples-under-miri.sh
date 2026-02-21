#!/usr/bin/env bash

set -eoux pipefail;

cargo +nightly miri run --example circular_buffer "${@}";
