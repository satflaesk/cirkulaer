#!/usr/bin/env bash

set -eoux pipefail;

cargo run --example basic "${@}";
cargo run --example ring_buffer "${@}";
