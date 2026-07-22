# Step 9 EC optimization closure and Blanc handoff

Date: 2026-07-22 (Asia/Seoul)

Status: **ELeVM short gates and final benchmarks are green. Final user-owned
FULL confirmation and the Blanc pin integration are pending.**

## Reviewed boundary

- ELeVM branch: `main`, clean and aligned with `origin/main`.
- ELeVM revision: `cefd732fe9d3310e283c27e09d0565835d4c93f6`.
- ELeVM toolchain: `leanprover/lean4:v4.23.0`.
- Native `elevm` SHA-256:
  `ff573c7a8fa7c1f752d810e9753b16f17b6992e86c5442d09112d3694095f845`.
- Native `elevm` size: 172,138,960 bytes.
- Blanc branch before integration: `main`, clean and aligned with
  `origin/main` at `c335118669d76fce30877cc1642bf4c9280f7bff`.
- Blanc toolchain: `leanprover/lean4:v4.23.0`.
- Blanc's `lakefile.lean`, `lake-manifest.json`, and managed checkout initially
  pin ELeVM `118b208acabd2c08f13f8391c9ae4685d48165f2`.

The ELeVM fixture roots for the four ordinary families, SMOKE, and the pinned
EEST BLS tier are present. The committed manifests still contain 175 SMOKE
files, 29 BLS files, 42 expected vector files (5 controls and 37 BLS/point
evaluation files), and 2,983 FULL baseline rows (2,978 PASS and 5 FAIL).

Lean LSP reported no diagnostics in `Elevm/EC.lean`, `Elevm/BLS.lean`,
`scripts/check-ec.lean`, or `scripts/bench-ec.lean`. A source and diff scan
found no added `sorry`, `admit`, axiom, `ofReduceBool`, or `ofReduceNat`.

## Retained commits, files, and definitions

The user-created commits are all reachable from `origin/main`:

| step | commit | message |
|---|---|---|
| 1 | `b3c113c11b4086bb01e19ed07be4e90f5f45f612` | `ec : step 1` |
| 2 | `bbae7dea7221fe96c37f09213bb9d1c84c133cb5` | `ec : step 2` |
| 3 | `87dadfe29632e1241682f73327edc7569735d58e` | `ec : step 3 (use Jacobian scalar multiplication)` |
| 4 | `7c6ef9fb5c3415cc752ad36a735e2c6cfe2d981d` | `ec : step 4 (use joint recovery multiply)` |
| 5 | `811f27a55fd503e896bd44fd444e81ebaea212c4` | `ec : step 5 (determine no-go for step 6)` |
| 7 | `cefd732fe9d3310e283c27e09d0565835d4c93f6` | `ec : step 7 (determine no-go for step 8)` |

The retained review scope relative to pre-plan revision `118b208` is exactly:

- `Elevm/EC.lean`: explicit fixed squares/cubes; private affine scalar
  reference; internal `EllipticCurve.JacobianPoint` and
  `EllipticCurve.Jacobian.{infinity,isInfinity,canonicalize,ofAffine,toAffine,double,add,mixedAdd,mulLoop}`;
  the stable affine `EllipticCurve.mulBy` wrapper; and
  `secp256k1.{recoverAffine,jointMulLoop,jointMul,recover}`.
- `scripts/bench-ec.lean`: the native EC rows plus Step-7 BN254/BLS full-pairing
  and Miller-only rows.
- `scripts/check-ec.lean`: the affine semantic oracle, Jacobian edge cases,
  joint multiplication cases, scalar sweeps, frozen degenerate cases, and the
  recovery matrix.
- `scripts/check-ec.sh` and `scripts/run-bench-ec.sh`: the native checker and
  benchmark wrappers.
- `scripts/report-ec-fixed-base-decision.md` and
  `scripts/report-ec-pairing-decision.md`: the two conditional decision
  records.
- this final closure report.

No production BLS module, public affine point type, infinity sentinel,
precompile signature, baseline, fixture target list, vector manifest, or gas
behavior changed. Public `EllipticCurve.add`, `EllipticCurve.double`,
`EllipticCurve.mulBy`, and `secp256k1.recover` signatures remain unchanged.
The test-only affine references and benchmark-only BN254 G2 generator are not
imported by `Elevm/`, `Elevm.lean`, or `Main.lean`. There is no generated table
or generated production artifact to reproduce.

Ignored benchmark reports remain measurement evidence only. The final raw
benchmark reports are under `/tmp/elevm-step9` and may be deleted after review;
no temporary reference implementation or report file is scheduled for
deletion from production imports because none leaked there.

## Final verification gates

| gate | final evidence | result |
|---|---|---|
| Lean LSP | four retained/current Lean files, no diagnostics | **PASS** |
| EC differential checker | 573/573 cases; about 11 s wall time | **PASS** |
| SMOKE | 175/175 baseline classifications; 174 PASS / 1 expected FAIL; 491.13 s summed file time | **PASS** |
| BLS | 29/29 target classifications; 29 PASS / 0 FAIL; 189.45 s summed file time | **PASS** |
| vectors (user-owned) | current report dated after the final Step-7 commit: 42/42 files, including 5/5 controls | **PASS** |
| FULL (user-owned Step-4 review run) | 2,983/2,983 baseline classifications; 2,978 PASS / 5 expected FAIL; 2,322.63 s summed file time | **PASS at the final production binary, but Step-9 rerun/confirmation pending** |

The FULL run completed immediately before the Step-4 commit and used the
native binary whose SHA-256 is recorded above. Steps 5 and 7 changed only
reports and the benchmark instrument, so production semantics and that native
binary did not change afterward. Nevertheless, Step 9 literally assigns the
final FULL gate to the user; Blanc integration remains blocked until the user
confirms whether this exact-binary run is accepted or supplies a fresh green
`scripts/check.sh --full --no-build` result. FULL remains a correctness gate,
not a performance goal, and the committed 55.6-minute reference is not
expected to fall below ten minutes.

## Native benchmark progression

Every scalar/recovery entry is a five-run median in ns/op using the same
committed native instrument, inputs, forcing boundary, optimization level, and
machine. Pairing rows were added only at Step 7, so no earlier comparable row
exists.

| row | Step 1 | Step 2 small-pow | Step 3 Jacobian | Step 4 joint | Step 9 final | Step 1 -> final |
|---|---:|---:|---:|---:|---:|---:|
| secp256k1 recovery | 49,188,387 | 48,866,228 | 4,813,892 | 2,124,163 | 2,140,882 | **22.98x** |
| secp256k1 scalar mul | 16,389,080 | 16,557,447 | 1,527,220 | 1,569,112 | 1,580,029 | **10.37x** |
| BN254 G1 scalar mul | 15,848,312 | 16,006,164 | 1,535,080 | 1,568,705 | 1,567,227 | **10.11x** |
| BLS12-381 G1 scalar mul | 23,881,575 | 24,257,309 | 1,625,794 | 1,649,822 | 1,610,219 | **14.83x** |
| BLS12-381 G2 scalar mul | 217,632,365 | 220,608,295 | 13,063,512 | 13,339,161 | 13,028,177 | **16.70x** |
| BN254 full pairing | - | - | - | - | 597,122,208 | - |
| BN254 Miller only | - | - | - | - | 69,970,500 | - |
| BLS12-381 full pairing | - | - | - | - | 916,441,917 | - |
| BLS12-381 Miller only | - | - | - | - | 55,218,500 | - |

All five final runs reproduced every sink. The final recovery runs ranged from
2,088,360 to 2,173,152 ns/op, a 4.0% max/min spread.

## Ordinary-directory factors and Amdahl comparison

The table sums the per-file report times for each reviewed directory. Step 4
uses the identical reruns recorded after the initial quantized measurements.
There is no separate Step-9 ordinary rerun because Steps 5 and 7 retained no
production change.

| stage | `vmArithmeticTest` | `stMemoryTest` | `stSStoreTest` | `stCallCodes` | aggregate | aggregate vs Step 1 |
|---|---:|---:|---:|---:|---:|---:|
| Step 1 baseline | 17.25 s | 44.42 s | 35.28 s | 8.86 s | 105.81 s | 1.000x |
| Step 2 small-pow | 17.24 s | 44.55 s | 34.49 s | 8.63 s | 104.91 s | 1.009x |
| Step 3 Jacobian | 7.31 s | 20.02 s | 13.20 s | 4.97 s | 45.50 s | 2.325x |
| Step 4/final production | 6.72 s | 16.44 s | 11.96 s | 4.66 s | 39.78 s | **2.660x** |

The planning model used a historical 70% EC / 30% residual split and a 15x EC
speedup, predicting `1 / (.70 / 15 + .30) = 2.88x`, with a 3.33x EC-only
asymptote. The achieved 2.660x aggregate is 7.6% below that predicted factor
but still removes 62.4% of the measured ordinary time. The difference is
consistent with the plan's explicit warning that the 70% split and 10--30x
recovery gain were hypotheses rather than guarantees. Step 3 exceeded its
gates (10.15x recovery and 56.6% aggregate-time reduction versus Step 2), and
Step 4 exceeded its gates (2.27x recovery and 12.6% aggregate-time reduction
versus Step 3).

## Conditional decisions and residual profiles

Step 5 recorded **NO-GO**, so Step 6 was skipped. Ecrecover was only
8.78--10.42% inclusive in the four ordinary profiles, not at least 15% in
three families. A width-4 joint-wNAF model predicted about a 12% recovery
reduction but only 1.15% aggregate time reduction (1.012x); even deleting all
recovery gave only a 1.106x ceiling. Keccak remained about 80--83% inclusive.

Step 7 recorded **BN254 NO-GO** and **BLS12-381 NO-GO**, so Step 8 was skipped.
The pairing profiles attributed only 4.14% (BN254) and 3.42% (BLS) inclusive
time to affine double/add, below the 20% gate. Even deleting the whole Miller
row gave only 11.88% and 5.99% full-pairing reductions, below the required
15%. The dominant residual is final exponentiation, field arithmetic, and
allocation; the plan correctly forbids broadening this EC project into that
separate field-representation effort.

Thus the only projection miss is the deliberately retained gap between the
historical 2.88x aggregate Amdahl estimate and the measured 2.660x. Both
conditional branches were rejected rather than rationalized from micro-only
gains.

## Baseline, manifest, and deviation accounting

- Baselines, SMOKE/BLS target lists, vector manifests, fixtures, public gas
  behavior, and generated artifacts are unchanged.
- No fixed-generator table was generated because Step 5 failed.
- No homogeneous-projective pairing implementation was added because both
  Step-7 families failed.
- No production BLS source changed.
- The only plan deviation awaiting resolution is whether the already-green
  exact-final-binary FULL result is accepted instead of a second Step-9 run.
- There are no unexplained tracked changes.

## Blanc protected boundary before pin update

At Blanc's original ELeVM pin, the protected theorem statements are:

```lean
theorem weth_inv_solvent (wa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post)  →
      (sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth) →
      Precond wa sevm pre →
      Postcond wa sevm post := by

theorem stateTransition_inv_solvent (wa : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state := by

theorem chain_inv_solvent (wa : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state := by

theorem addBlockToChain_inv_solvent (wa : Adr)
    (ch ch' : BlockChain) (rlp : B8L)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state := by
```

The pre-integration Blanc audit passed 4/4, and every theorem used exactly
`[propext, Classical.choice, Quot.sound]`. These statements and exact axiom
sets must be rechecked after the pin update; a pre-integration result is not a
substitute for the final gate.

## Pending handoff

After user-owned FULL confirmation, the remaining sequence is:

1. if this report is retained, user review/commit/push it so the final ELeVM
   revision is a reachable 40-character commit;
2. update only Blanc's `lakefile.lean` and `lake-manifest.json` pin and the
   normal Lake-managed checkout to that pushed ELeVM revision;
3. run Blanc's full `scripts/check.sh` gate;
4. re-audit the four theorem statements and exact axiom sets; and
5. leave the Blanc pin bump uncommitted for user review.

Suggested ELeVM report commit: `docs(perf): record EC optimization closure`.
The eventual Blanc commit remains user-owned; because the pairing rewrite was
NO-GO, a precise message is `chore: pin EC optimization` rather than the
plan's now-inaccurate projective-pairing wording.

The only evidence-backed follow-up is a separately scoped investigation of
the final-exponentiation/field-arithmetic/allocation residual. It is not a
continuation of the rejected projective Miller-loop or fixed-base branches and
must receive its own baseline, profile, and decision gate.
