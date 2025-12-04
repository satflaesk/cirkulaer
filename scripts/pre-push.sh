#!/usr/bin/env bash

set -eoux pipefail;

./scripts/build-all-targets.sh;
./scripts/check-coverage.sh;
./scripts/check-example-in-readme-file.sh;
./scripts/check-formatting.sh;
./scripts/generate-documentation.sh;
./scripts/run-all-examples.sh;
./scripts/run-all-tests.sh;
./scripts/run-clippy.sh;
