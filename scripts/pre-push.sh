#!/usr/bin/env bash

# To automatically run this script before pushing, navigate to the root directory of the repository
# and issue the following sequence of commands:
#
# $ mkdir --parents .git/hooks
# $ cd .git/hooks
# $ ln --symbolic ../../scripts/pre-push.sh pre-push

set -eoux pipefail;

repo_root=$(git rev-parse --show-toplevel);
pushd "${repo_root}/scripts";

./build-all-targets.sh;

./check-coverage.sh;
./check-formatting.sh;
./generate-documentation.sh;
./run-all-examples-under-miri.sh;
./run-all-examples.sh;
./run-all-tests-under-miri.sh;
./run-all-tests.sh;
./run-clippy.sh;

./run-all-benchmarks.sh;

popd;
