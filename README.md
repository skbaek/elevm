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

[^1]:As of 2025/09/19, commit [`4198...7694`](https://github.com/ethereum/execution-specs/tree/4198b9c5996713b268aed602739d5aa40e277694)