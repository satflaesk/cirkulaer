#!/usr/bin/env bash

set -eoux pipefail;

repo_root=$(git rev-parse --show-toplevel);
pushd "${repo_root}/scripts";

./build-all-targets.sh
./build-all-targets.sh --no-default-features
./build-all-targets.sh --no-default-features --features std

./check-coverage.sh;
./check-formatting.sh;
./generate-documentation.sh;
./run-all-examples-under-miri.sh;
./run-all-examples.sh;
./run-all-tests-under-miri.sh;
./run-all-tests.sh;
./run-all-tests.sh --release;
./run-clippy.sh;

./run-all-benchmarks.sh;

popd;
