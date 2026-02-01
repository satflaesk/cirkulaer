#!/usr/bin/env bash

set -eoux pipefail;

cargo run --example ring_buffer "${@}";
