#!/usr/bin/env bash

set -eoux pipefail;

expected_tail_of_readme_file=$(mktemp --suffix=.expected);
cat <(printf '```rust\n') examples/basic.rs <(printf '```\n') >> "${expected_tail_of_readme_file}";

num_lines_in_expected_tail=$(cat "${expected_tail_of_readme_file}" | wc --lines);
actual_tail_of_readme_file=$(mktemp --suffix=.actual);
tail -"${num_lines_in_expected_tail}" README.md >> "${actual_tail_of_readme_file}";

diff "${expected_tail_of_readme_file}" "${actual_tail_of_readme_file}";

rm "${expected_tail_of_readme_file}" "${actual_tail_of_readme_file}";
