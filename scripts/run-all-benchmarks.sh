#!/usr/bin/env bash

set -eoux pipefail;

cargo bench --bench addition_assignment "${@}";
