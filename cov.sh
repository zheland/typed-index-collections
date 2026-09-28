#!/usr/bin/env bash

cargo +nightly llvm-cov --doctests --all-features
cargo +nightly llvm-cov --doctests --all-features --html
