#!/usr/bin/env bash

set -eoux pipefail;

source_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &> /dev/null && pwd);
destination_dir="$(git rev-parse --show-toplevel)/.git/hooks";

mkdir --parents "${destination_dir}";
pushd "${destination_dir}";

pre_commit_script=$(realpath --no-symlinks --relative-to "${destination_dir}" "${source_dir}/pre-commit.sh");

ln --interactive --symbolic "${pre_commit_script}" pre-commit;

popd;
