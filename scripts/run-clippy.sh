#!/usr/bin/env bash

set -eoux pipefail;

cargo clippy "${@}";
