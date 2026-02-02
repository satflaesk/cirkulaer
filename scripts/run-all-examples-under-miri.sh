#!/usr/bin/env bash

set -eoux pipefail;

cargo miri run --example ring_buffer "${@}";
