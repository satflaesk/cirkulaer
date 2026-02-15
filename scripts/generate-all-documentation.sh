#!/usr/bin/env bash

set -eoux pipefail;

cargo doc --document-private-items "${@}";
