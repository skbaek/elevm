# Step 5 fixed-generator residual decision

Date: 2026-07-22 (Asia/Seoul)

Verdict: **NO-GO. Skip Step 6.**

## Reviewed boundary and scope

Profiling was performed on the reviewed Step-4 boundary:

- branch: `main`, aligned with `origin/main`;
- commit: `7c6ef9fb5c3415cc752ad36a735e2c6cfe2d981d`;
- initial and post-profiling working tree: clean;
- native `elevm` SHA-256:
  `ff573c7a8fa7c1f752d810e9753b16f17b6992e86c5442d09112d3694095f845`;
- native `elevm` size: 172,138,960 bytes; and
- native EC benchmark size: 172,056,384 bytes.

The executable timestamp postdated the Step-4 `Elevm/EC.lean` source. The
benchmark was compiled from the same current Lake native dependency-object
trace using Lean C generation followed by `leanc -O2`.

No production code, baseline, target manifest, or vector manifest was edited.
This decision report is the sole final worktree addition.
Raw profiles and benchmark reports were written under `/tmp/elevm-step5`. A
temporary 20,000-iteration copy of the unchanged recovery benchmark, used only
to keep the process alive for sampling, was placed under the gitignored
`.lake/build/step5` directory.

## Commands and measurement method

The five current benchmark repetitions used the committed wrapper and
instrument:

```sh
cd ~/elevm
for i in 1 2 3 4 5; do
  ELEVM_REPORT_DIR=/tmp/elevm-step5 \
    scripts/run-bench-ec.sh "step5-residual-$i"
done
```

Symbol presence was checked in both the reviewed executable and freshly linked
benchmark:

```sh
nm .lake/build/bin/elevm
nm /tmp/elevm-step5/bench-ec
```

Representative resolvable symbols included:

- `secp256k1_recover` and the concrete private `secp256k1_jointMulLoop`;
- the joint-loop Jacobian full-add specialization and the concrete Jacobian
  double, mixed-add, and final-normalization specializations;
- `FinField_mul`, `lean_nat_big_mod`, `FinField_inv`, and `extEuclid`;
- `B8L_keccak`; and
- runtime/allocation frames including `lean_alloc_ctor`, `lean_apply_2`, and
  `lean_dec_ref_cold`.

The recovery microprofile and four ordinary families used macOS `sample` with
a 1 ms interval, a maximum duration of 25 seconds, and `-mayDie`:

```sh
<native-process> &
pid=$!
sample "$pid" 25 1 -mayDie -file "$profile"
wait "$pid"
```

The ordinary processes were the reviewed `.lake/build/bin/elevm` executable
applied directly to these canonical directories:

```text
~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests/GeneralStateTests/VMTests/vmArithmeticTest
~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests/GeneralStateTests/stMemoryTest
~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests/GeneralStateTests/stSStoreTest
~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests/GeneralStateTests/stCallCodes
```

All attribution below is based on the main-thread inclusive call tree. For a
recursive or repeated category, only its top-most occurrence on a sampled
stack was counted, so time caused by a category remains attributed to it rather
than being double-counted at each recursive frame. Categories in the table are
not mutually exclusive and therefore overlap.

## Current recovery benchmark

Every run reproduced the committed sink value `226967009`.

| run | `secp256k1-recover` |
|---:|---:|
| 1 | 2,047,690 ns/op |
| 2 | 2,115,180 ns/op |
| 3 | 2,124,859 ns/op |
| 4 | 2,038,174 ns/op |
| 5 | 2,101,649 ns/op |
| **median** | **2,101,649 ns/op** |

The Step-4 median was 2,124,163 ns/op. The Step-5 median is 1.06% lower,
which is consistent with ordinary run-to-run variation and does not represent
a code change.

## Inclusive residual profiles

| workload | samples | ecrecover | joint loop | double | mixed add | full add | field mul | big-Nat mod | normalization | `extEuclid` | keccak | allocation/refcount/free |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| recovery micro | 21,119 | 99.94% | 87.09% | 42.63% | 27.18% | 14.54% | 34.01% | 26.91% | 2.09% | 3.92% | 2.64% | 66.95% |
| `vmArithmeticTest` | 5,191 | **8.78%** | 7.36% | 3.70% | 2.25% | 1.25% | 2.64% | 2.33% | 0.21% | 0.35% | 82.59% | 53.75% |
| `stMemoryTest` | 13,167 | **9.32%** | 8.26% | 3.96% | 2.58% | 1.47% | 3.14% | 2.31% | 0.17% | 0.37% | 81.27% | 52.15% |
| `stSStoreTest` | 9,745 | **10.42%** | 9.03% | 4.15% | 2.98% | 1.78% | 3.76% | 3.06% | 0.22% | 0.37% | 80.56% | 52.99% |
| `stCallCodes` | 1,846 | **9.64%** | 8.23% | 3.63% | 3.20% | 1.08% | 3.63% | 3.14% | 0.22% | 0.38% | 81.15% | 50.22% |

The principal residual ordinary-workload bottleneck is now keccak at roughly
80--83%, rather than recovery. Allocation, GMP, and Lean refcount/free work
also remain substantial, but overlap the keccak and EC subtrees and are not a
separate additive share. Inside recovery, field multiplication/modulo and the
associated allocation traffic dominate the projective operations. Final
normalization is only about 2.1% of the recovery microprofile and 0.17--0.22%
of ordinary inclusive time.

## Fixed-generator operation model

The evaluated small design was width-4 joint wNAF:

- eight generated affine odd multiples `G, 3G, ..., 15G`, with negative
  digits obtained by negating `y` rather than duplicating the table;
- eight runtime Jacobian odd multiples of the dynamic recovered point `R`;
- one dynamic precomputation double and seven dynamic full additions;
- generated fixed constants outside handwritten Lean source; and
- no constant-time table-access claim.

The raw fixed table would contain 8 affine points, or 512 bytes of coordinates
before Lean/native representation overhead. The dynamic table would contain 8
Jacobian points, or 768 raw coordinate bytes before boxed-Nat and container
overhead.

For the 200 committed benchmark inputs, the current joint binary method
averages:

- 117.00 set bits in the `R` coefficient;
- 128.49 set bits in the `G` coefficient;
- 58.26 positions where both are set; and
- 187.24 joint point additions in total.

Width-4 wNAF averages 51.00 nonzero `R` digits and 52.13 nonzero `G` digits.
Including the seven dynamic precomputation additions gives approximately
110.13 point additions, saving about 77.1 additions (41%) while increasing
the double count from 256 to 257.

Weighting those counts by the measured microprofile changes the double,
mixed-add, and full-add contribution from approximately 84.35% of recovery to
68.26%. This is an idealized 16.1% recovery-time reduction before signed
recoding, table indexing, selection, negation, and additional allocation. A
conservative projection after those costs is approximately a 12% reduction in
recovery time.

The measured ecrecover share weighted by all four ordinary sample counts is
9.60%. Amdahl projections are therefore:

| model | aggregate time reduction | aggregate speedup |
|---|---:|---:|
| conservative 12% recovery reduction | 1.15% | 1.012x |
| idealized 16.1% recovery reduction | 1.55% | 1.016x |
| impossible ceiling: remove all recovery | 9.60% | 1.106x |

Even the impossible ceiling misses the plan's aggregate 1.11x threshold.

## Literal gate application

Step 5 required both:

1. ecrecover at least 15% inclusive in at least three ordinary families; and
2. a conservative prediction of at least 10% further whole-workload
   improvement (about 1.11x).

Measured results:

- threshold 1: **FAIL**, because 0 of 4 families reached 15%; and
- threshold 2: **FAIL**, because the conservative aggregate prediction is
  about 1.15% less time, or 1.012x.

Therefore the fixed-generator decision is **NO-GO**. Step 6 is skipped. A
micro-only fixed-base improvement is not sufficient under the predeclared
ordinary-workload rule.

## Verification and handoff

After profiling, the required differential checker was run without modifying
its tracked report:

```sh
cd ~/elevm
ELEVM_REPORT_DIR=/tmp/elevm-step5 scripts/check-ec.sh
```

Result: **573/573 PASS**.

No vector or FULL rerun belongs to this no-diff Step-5 gate; the user had
already reported both Step-4 review-boundary gates green. No production diff
or implementation commit exists. The next plan action is Step 7, the
independent residual decision gate for projective pairing loops.
