#!/usr/bin/env bash

set -eoux pipefail;

cargo miri test "${@}";
