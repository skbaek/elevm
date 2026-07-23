# ELEVM

Executable Lean EVM (ELEVM) is an implementation of the Ethereum Virtual Machine 
(EVM) in the Lean 4 theorem prover. ELEVM can run EVM state tests in the standard JSON 
format of [execution spec tests](https://github.com/ethereum/execution-spec-tests). 
It passes all general state tests used by the latest version[^1] of 
[execution-specs](https://github.com/ethereum/execution-specs) on the `mainnet` branch.

## Prerequisite

You need to have [elan](https://github.com/leanprover/elan) installed.

## Installation

`lake build`

## Usage

`lake exe elevm /path/to/test`

## External test fixtures

The fixture suites use pinned data outside this repository. See
[`scripts/vectors/SOURCES.md`](scripts/vectors/SOURCES.md) for the safe
execution-specs/legacy-fixture and EEST bootstrap, frozen Python oracle,
environment doctor, path overrides, disk requirements, and long-test
requirements.

## Portability checks in CI

CI preserves the ordinary Lean build and separately runs the standard-library
unit suite for the source manifest, read-only doctor, legacy/EEST/oracle
bootstraps, malicious archive handling, and generator path/pin checks. The
tests create only tiny synthetic Git repositories and fixture archives in their
temporary workspace; CI never downloads the EEST release or a complete legacy
fixture corpus.

The workflows intentionally use maintained major-version action tags
(`actions/checkout@v6`, `actions/setup-python@v5`, and
`leanprover/lean-action@v1`) instead of immutable commit SHAs. Review the
corresponding official action release notes before a tag update, and keep that
policy consistent within ELEVM.

[^1]:As of 2025/09/19, commit [`4198...7694`](https://github.com/ethereum/execution-specs/tree/4198b9c5996713b268aed602739d5aa40e277694)
