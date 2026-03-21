#!/usr/bin/env bash

set -eoux pipefail;

RUSTDOCFLAGS="-D warnings" cargo doc "${@}";
