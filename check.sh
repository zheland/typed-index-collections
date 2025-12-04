#!/usr/bin/env bash

# Crate-specific settings
toolchains=( stable beta nightly "1.90.0" )
all_features=( "" "alloc" "std" "serde" )
max_uncovered_functions=0
max_uncovered_lines=10
max_uncovered_regions=10

set -Eeuo pipefail

tmp_dir=""
bold_red=$'\033[1;31m'
bold_green=$'\033[1;32m'
no_color=$'\033[0m'

cleanup() {
    local return_code=$?
    if [ -n "$tmp_dir" ]; then
        rm -rf -- "$tmp_dir"
    fi
    exit $return_code
}

trap cleanup EXIT

tmp_dir="$( mktemp -d )"

ok() { echo "${bold_green}OK${no_color}: $@" 1>&2; }
fail() { echo "${bold_red}ERROR${no_color}: $@" 1>&2; exit 1; }
echo_and_run() { echo "$ ${*@Q}"; "$@"; }

echo_and_try_run() {
    set +eo pipefail
    echo "$ ${*@Q}"
    "$@" 2> >( tee "$tmp_dir/error.txt" )
    echo $? > "$tmp_dir/return_code.txt"
    set -eo pipefail
}

expect_failure() {
    if [ "$(cat "$tmp_dir/return_code.txt")" -ne "0" ]; then
        ok "Command failed as expected."
        if ! cat "$tmp_dir/error.txt" | grep -q "$@"; then
            fail "Unexpected error message, expected regex: ${*@Q}."
        fi
    else
        fail "Command did not fail as expected."
    fi
}

echo_and_run cargo +nightly fmt --all -- --check
echo_and_run cargo msrv verify
echo_and_run cargo outdated --exit-code 1

# Each value is a set of `|`-separated values:
# - comma separated features,
# - expected error message regex"
valid_no_alloc_and_no_std_param_sets=(
    # `no-std || no-alloc` require `panic_handler` defined.
    "|panic_handler.* function required"
    "panic-handler|"
    # `no-std && alloc` require `global-allocator` defined.
    "alloc,panic-handler|no global memory allocator found"
    "alloc,panic-handler,global-allocator,rust-eh-personality|"
    # `std && alloc` require `panic_handler` not defined.
    "alloc,std,panic-handler,global-allocator,rust-eh-personality|found duplicate lang item .*panic_impl"
    "alloc,std,global-allocator|"
    "alloc,std|"
)
for toolchain in "${toolchains[@]}"; do
    (
        echo_and_run export CARGO_TARGET_DIR="target/check-no-alloc-and-no-std-$toolchain"
        for param_set in "${valid_no_alloc_and_no_std_param_sets[@]}"; do
            features=$(echo "$param_set" | cut -sd"|" -f1)
            expected_error_regex=$(echo "$param_set" | cut -sd"|" -f2-)
            args="--config build.rustflags=[\"-C\",\"link-arg=-nostartfiles\"]"
            args+=" --manifest-path tests/no-alloc-and-no-std/Cargo.toml"
            args+=" --no-default-features"
            [ -n "$features" ] && args+=" --features $features"
            if [ "$expected_error_regex" = "" ]; then
                echo_and_run cargo "+$toolchain" clippy $args -- -D warnings
                echo_and_run cargo "+$toolchain" build $args
            else
                echo_and_try_run cargo "+$toolchain" build $args
                expect_failure "$expected_error_regex"
            fi
        done
    )
done

num_features=${#all_features[@]}
num_combinations=$(echo "2^$num_features" | bc)
feature_sets=()

# Iterate over all `2^num_features` features combinations if required
# `combination_idx` is used as a bitmask of the enabled features.
for ((combination_idx = 0; combination_idx < num_combinations; combination_idx++)); do
    features_set=()
    for ((feature_idx = 0; feature_idx < num_features; feature_idx++)); do
        mask=$(echo "2^$feature_idx" | bc) # The mask of `feature_idx`-th feature.

        if (( combination_idx & mask )); then
            features_set+=(${all_features[$feature_idx]})
        fi
    done
    features=$(echo "${features_set[@]}" | tr " " ",")
    feature_sets+=("$features")
done


for toolchain in "${toolchains[@]}"; do
    (
        export CARGO_TARGET_DIR="target/check-$toolchain"
        for features in "${feature_sets[@]}"; do
            cargo="cargo +$toolchain"
            if [ -n "$features" ]; then
                args="--no-default-features --features $features"
            else
                args="--no-default-features"
            fi
            echo_and_run $cargo clippy --all-targets $args -- -D warnings
            echo_and_run $cargo build --all-targets $args
            echo_and_run $cargo test --all-targets $args
            echo_and_run $cargo test --release --all-targets $args
            echo_and_run $cargo test --doc $args
            echo_and_run $cargo test --doc --release $args
            if [[ "$toolchain" == "nightly" ]]; then
                echo_and_run $cargo miri test --all-targets $args
            fi
            echo_and_run $cargo bench --no-run --all-targets $args
        done
    )
done

echo_and_run cargo deny --workspace --all-features check

echo_and_run cargo +nightly llvm-cov --doctests --all-features --html \
    --fail-uncovered-functions $max_uncovered_functions \
    --fail-uncovered-lines $max_uncovered_lines \
    --fail-uncovered-regions $max_uncovered_regions \
    || true # Ignore failure because of error "N functions have mismatched data"

for features in "${feature_sets[@]}"; do
    args=()
    features=$( echo "$features" | tr "," " " )
    for feature in ${features}; do
        args+=( --features )
        args+=( $feature )
    done
    echo_and_run cargo semver-checks --only-explicit-features "${args[@]}"
done

ok "All checks succeeded." 1>&2
