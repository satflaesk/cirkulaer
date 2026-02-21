#!/usr/bin/env bash

set -eoux pipefail;

cargo run --example circular_buffer "${@}";
