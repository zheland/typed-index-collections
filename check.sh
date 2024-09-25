#!/usr/bin/env bash

set -Eeuo pipefail

echo_and_run() { echo "$ ${*@Q}"; "$@"; }
fail() { echo "$@" 1>&2 ; exit 1; }

expect_failure() {
    error_file=$( mktemp )
    set +eo pipefail
    echo_and_run eval "$1" 2> >( tee "$error_file" )
    [ $? != 0 ] && echo -e "    \033[1;32mOK\033[0m: Command failed as expected" \
        || fail "Command did not fail as expected"
    cat "$error_file" | grep -q "$2" || fail "Unexpected error message"
    set -eo pipefail
    rm "$error_file"
}

echo_and_run cargo +nightly fmt --all -- --check
echo_and_run cargo outdated --exit-code 1

(
    export CARGO_TARGET_DIR="$PWD/target/check-no-alloc-and-no-std"
    echo_and_run cd tests/no-alloc-and-no-std

    echo_and_run cargo build --features panic-handler
    echo_and_run cargo build --features alloc,panic-handler,global-allocator
    echo_and_run cargo build --features alloc,std,global-allocator

    expect_failure "cargo build" \
        'panic_handler.* function required'
    expect_failure "cargo build --features alloc,panic-handler" \
        'no global memory allocator found'
    expect_failure "cargo build --features alloc,std,panic-handler,global-allocator" \
        'found duplicate lang item .*panic_impl'
)

toolchains=( stable beta nightly "1.81.0" )
feature_sets=( "" "alloc" "std" "serde" "serde-alloc" "std serde-alloc" "serde-std")

for toolchain in "${toolchains[@]}"; do
    for features in "${feature_sets[@]}"; do
        (
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
        )
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

echo_and_run cargo deny --workspace --all-features check

echo_and_run cargo +nightly llvm-cov --doctests --all-features --html \
    --fail-uncovered-functions 0 \
    --fail-uncovered-lines 10 \
    --fail-uncovered-regions 10

echo "All checks succeeded." 1>&2
