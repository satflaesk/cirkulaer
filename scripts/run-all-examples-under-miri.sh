#!/usr/bin/env bash

set -eoux pipefail;

cargo +nightly miri run --example ring_buffer "${@}";
