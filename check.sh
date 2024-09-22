#!/usr/bin/env bash

set -Eeuo pipefail

echo_and_run() { echo "$ ${*@Q}"; "$@"; }

toolchains=( stable beta nightly "1.81.0" )
feature_sets=( "" "alloc" "std" "serde-alloc" "serde-alloc std" "serde-std")

echo_and_run cargo +nightly fmt --all -- --check
echo_and_run cargo outdated --exit-code 1

for toolchain in "${toolchains[@]}"; do
    for features in "${feature_sets[@]}"; do
        export CARGO_TARGET_DIR="target/check-$toolchain"
        echo_and_run cargo "+$toolchain" clippy --all-targets \
            --no-default-features --features "$features" -- -D warnings
        echo_and_run cargo "+$toolchain" build --all-targets \
            --no-default-features --features "$features"
        echo_and_run cargo "+$toolchain" test --all-targets \
            --no-default-features --features "$features"
        echo_and_run cargo "+$toolchain" test --release --all-targets \
            --no-default-features --features "$features"
        echo_and_run cargo "+$toolchain" test --doc \
            --no-default-features --features "$features"
        echo_and_run cargo "+$toolchain" test --doc --release \
            --no-default-features --features "$features"
        if [[ "$toolchain" == "nightly" ]]; then
            echo_and_run cargo "+nightly" miri test --all-targets \
                --no-default-features --features "$features"
        fi
        echo_and_run cargo bench --no-run --all-targets \
            --no-default-features --features "$features"
    done
done

for features in "${feature_sets[@]}"; do
    args=()
    for feature in ${features}; do
        args+=( --features )
        args+=( $feature )
    done
    echo_and_run cargo semver-checks --only-explicit-features "${args[@]}"
done

echo_and_run deny --workspace --all-features check

echo "All checks are successful." 1>&2
