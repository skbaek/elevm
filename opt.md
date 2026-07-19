# Patch plan: EVM word performance — algorithms first, representation second

This is a self-contained implementation plan for `/Users/bsk/elevm` and its
downstream proof client `/Users/bsk/blanc`: harvest the measured word-op
performance wins in **cost order** — cheapest churn first — instead of
leading with a representation migration. It supersedes `~/u256.md` as the
execution plan after the critique in `~/u256-critique.md` (working evidence:
`~/blanc/u256-critique-wip.md`) was verified against both repositories:
the critique's factual claims all held, and the old plan's own benchmark
table shows that its headline wins (100–200× division, ~6× mul, the EXP
collapse) are **algorithm** wins collectable on the incumbent pair
representation, while only the ~9× add/bitwise/compare rows are bound to
the flat-limb representation. The old plan's durable assets — the flat
4×`UInt64` design, the `BitVec 256` proof model, the golden-vector oracle,
the semantic-trap inventory — are preserved here as **Phase B**, gated
behind a measured go/no-go decision. It follows the style and discipline of
`~/blanc/precomps.md`: one sequential, agent-session-sized step at a time;
one commit per touched repository per step; explicit verification gates; no
long blind arcs.

**Phase A: 7 unconditional steps** (worst case 9 sessions with sanctioned
splits inside Steps 5 and 6). **Phase B: 5 conditional steps** (8–12),
entered only if Step 7's pre-registered thresholds say the representation
still matters after the cheap wins are banked. Step 1 builds the
correctness oracle and instruments; Steps 2–3 replace the O(bits)
arithmetic algorithms on the *unchanged* pair type; Step 4 is the first
cross-repo integration and is **net-negative in proof lines**; Steps 5–6
attack the two non-arithmetic timeouts (decode churn, precompile inner
loops); Step 7 harvests, re-profiles, and decides Phase B honestly.

**Precondition**: both trees clean at plan-writing state — elevm `28692ee`
(`add minimal CI`), blanc `f7ff19a` (`add minimal CI`), blanc's dependency
git-pinned to elevm `f621e16`. The untracked `~/blanc/u256-critique-wip.md`
is the user's to commit or remove before Step 1; it is not part of this
plan's commits. `~/u256.md` is retired as an execution plan; do not
interleave this arc with any other.

## Starting point (verified at plan-writing time)

### The performance picture (the targets)

- FULL tier: 2983 fixture files; **4 TIMEOUTs** (per-file limit 100 s):
  `vmPerformance/loopExp.json`, `vmPerformance/loopMul.json`,
  `stTimeConsuming/CALLBlake2f_MaxRounds.json`,
  `stTimeConsuming/static_Call50000_sha256.json`; **5 FAILs**, all in
  intrinsic-gas / invalid-block families (`intrinsicCancun`,
  `bcEIP1559/intrinsicOrFailCancun`, `bcStateTests/EmptyTransaction`,
  `UserTransactionGasLimitIsTooLowWhenZeroCost`, `txCost-sec73`) —
  correctness work, out of this plan's scope. SMOKE contains `loopMul` and
  the sha file. BLS tier: all-PASS, **no sanctioned TIMEOUT**
  (`baseline-bls.txt` says so explicitly); `test_valid.json` completes in
  ~265–285 s under its 1200 s limit. The old plan's expectation that
  `test_valid.json` is a permanent TIMEOUT is stale — never resurrect it.
- Attribution (sampled at plan-writing time on the optimized binary; raw
  data in `~/blanc/u256-critique-wip.md`):
  - **loopExp** — the only word-arithmetic-bound offender: samples land in
    `B256.bexpCore` / `B256.mul` / `B128.mulx` / `B64.mulx` + allocation.
  - **loopMul** — decode-bound, *not* multiplication: per-step re-decode
    plus `B8L.toB256` (`pack`/`take`/`drop`) list churn.
  - **Blake2F** — entirely in its own `Array B64` G-loop
    (`Blake2.g`, `Execution.lean:3043`); `B256` representation irrelevant.
  - **sha256×50000** — unprofiled; SHA-256 is a Lean port
    (`Hash.lean:125-263`, `SHA256.run`).
  - **BLS** — field inversion / affine EC arithmetic / final
    exponentiation (`GaloisField.pow`, `FinField.inv`, `extEuclid`);
    unrelated to `B256`, excluded (D8).

### The algorithms being replaced (representation untouched in Phase A)

- `B256.bexp`: **fixed 256-round ladder** (`bexpCore`,
  `Basic.lean:569-579`) — ~512 pair-multiplications per EXP regardless of
  exponent. `Nat.powMod` (square-and-multiply, early exit) already exists
  at `Basic.lean:582-591`.
- `B256.divMod`: **255-iteration shift-subtract**
  (`divOffset`/`divModCore`, `Basic.lean:507-535`); measured 25–54 µs per
  DIV.
- `B256.mul`: `mulx` schoolbook (`Basic.lean:500-505`), ~551 ns.
- `addmod`/`mulmod`: **already `Nat`/GMP-routed** (`Basic.lean:405-413`) —
  the routing pattern this plan generalizes. `Nat.toB256` exists
  (`Basic.lean:121`).
- Decode: `exec` re-fetches `getInst` **every step**
  (`Execution.lean:4004`, decode at `:1675-1693`); each PUSH execution
  slices the `ByteArray` into a `B8L` and runs `B8L.toB256`
  (`pack 32` → `take 16`/`drop 16` → `B128`/`B64` assembly,
  `Basic.lean:1228-1233`). CALLDATALOAD uses the same codec
  (`Execution.lean:2191`).
- `signext` builds a 32-byte list per call (`Basic.lean:415-422`) — noted,
  not a timeout driver; optional target only.

### Blanc exposure map (verified — what each change costs downstream)

Blanc depends on elevm via git pin (`lakefile.lean:12-13` @ `f621e16`), so
**elevm changes are invisible to blanc until a pin bump**; blanc repairs
happen only at the named integration steps (D5). Exposure per change:

- **EXP / div / mod / sdiv / smod: zero proof exposure.** `B256.bexp` is
  *applied* once (`Common.lean:4261`) and never unfolded; no blanc
  reference to `divMod`/`divOffset` exists.
- **mul: one exposed development.** `Solvent.lean` ~6843–7166 (~320 lines)
  proves `B256.toNat_mul : (x * y).toNat = (x.toNat * y.toNat) ↾ 256` by
  unfolding `mulx` (`B64.toNat_mulx`, `B128.toNat_mulx` + carry helpers),
  consumed at exactly **one** site (`Solvent.lean:7196`,
  `processWithdrawalsState_inv_solvent`). Blanc-local
  `toNat_toB256` (`Common.lean:1412`) makes the post-routing re-proof a
  2-liner. Net effect of Step 4: ~320 proof lines deleted, ~5 added.
- **Decode: bounded but real exposure.** `getInst` is load-bearing —
  `Semantics.lean:183-187` defines `Ninst.At`/`Linst.At`/… over it;
  `Ninst.run` is unfolded by `simp only [Ninst.run]`
  (`Semantics.lean:1028-1093`); `B8L.toB256` is unfolded in exactly two
  proofs (`Common.lean:1315-1318`, `:6766`). Consequence (D6): only the
  *codec implementation* may change; `getInst`/`Inst`/`Ninst.run`/`exec`
  shapes stay.
- The four protected theorems (`weth_inv_solvent`,
  `stateTransition_inv_solvent`, `chain_inv_solvent`,
  `addBlockToChain_inv_solvent`) keep building with unchanged statements
  at every integration boundary.
- Hash instances are **not** touched by this plan and must be preserved
  verbatim: `Hashable Adr` = low 64 bits (`Execution.lean:745`);
  `Hashable (Adr × B256)` mixes the address hash with **all four** B256
  limbs plus committed regression keys (`Execution.lean:749-763`,
  finding 3.9). Any Phase-B work re-inventories these instance-by-instance.

### Measurements that fix the design (arm64 macOS, Lean v4.23.0, `leanc -O2`, 2026-07-18)

The micro-benchmark table from the retired plan remains the evidence base
(ns/op; methodology note: results must be forced between the clock reads —
the Step-1 committed bench documents this pitfall):

| op            | pairs (current) | `BitVec 256` | `Nat`+mask | flat 4×`UInt64` |
|---------------|----------------:|-------------:|-----------:|----------------:|
| add (big)     | 61              | 251          | 149        | **7**           |
| add (small)   | 59              | 90           | 57         | —               |
| and (big)     | 95              | 338          | 245        | **14**          |
| lt  (big)     | 60              | 349          | 179        | **17**          |
| mul (big)     | 551             | 134          | **89**     | (not impl.)     |
| div ÷2¹²⁸     | 25 517          | 319          | **237**    | (via `Nat`)     |
| div ÷3        | 53 598          | 348          | **254**    | (via `Nat`)     |

Re-read with attribution discipline, three verdicts follow:

1. **The div/mul/exp columns are algorithm wins.** They come from routing
   through `Nat`/GMP and from killing fixed-round loops — available on the
   incumbent pairs today, exactly as `addmod`/`mulmod` already demonstrate.
   Phase A collects them at near-zero structural churn. (Caveat, honestly
   held: `Nat`-routed mul *on pairs* pays two `toNat`/`toB256` conversions
   the `Nat`+mask column does not; expect ~150–250 ns, not 89 — still ≥2×
   over 551. Step 3 measures before claiming.)
2. **Only add/and/lt are representation-bound** (~9× for flat limbs).
   Whether that matters end-to-end is *unproven*: no current timeout is
   bound on those ops. Hence Phase B is conditional (D7).
3. **`BitVec 256` at runtime stays rejected** (measured 4–6× slower than
   even the pairs). In Phase B it is the specification model only.

Plan-time per-file evidence (same machine): `blake2F.json` precompile
vectors 5.13 s for 5 cases, dominated by one 8,000,000-round case;
`blsG2MultiExp.head.json` 225 s — both untouched by anything in Phase A,
expectation registered now so Step 7's report is judged fairly.

## Reference implementations (all already on this machine)

- **EELS** — semantics oracle for the vector generator:
  `~/execution-specs/src/ethereum/prague/vm/instructions/{arithmetic,comparison,bitwise,keccak}.py`
  and `.../vm/gas.py`. Every vector is derived from local EELS source at
  generation time; the generator records
  `git -C ~/execution-specs rev-parse HEAD` in the emitted JSON header.
- **Existing elevm precedents** to imitate, not reinvent:
  `addmod`/`mulmod` `Nat` routing (`Basic.lean:405-413`), `Nat.powMod`
  (`Basic.lean:582-591`), the `--vectors` runner pattern
  (`Main.lean`, `scripts/check-vectors.sh`), `scripts/check.sh --dir` for
  per-file targeted gates, the generated-artifact discipline of
  `scripts/gen-bls-consts.py`.
- **Phase B only**: Lean core `Init.Data.BitVec.*`, `Std.Tactic.BVDecide`,
  the `UInt64.toBitVec` bridge (verified resolvable at plan-writing time);
  geth `uint256.Int` / revm `U256` as design precedent (no code ported).

## Correctness oracle and measurement instruments

- **Golden op vectors** (Step 1): `scripts/gen-u256-vectors.py` emits
  `scripts/vectors/u256.json` — ≥600 vectors covering every `B256` op the
  interpreter calls (add, sub, mul, div, mod, sdiv, smod, addmod, mulmod,
  exp + `bytecount`, signextend, lt/gt/slt/sgt/eq/iszero, and/or/xor/not,
  byte, shl/shr/sar, `toB8L`/`ofB8L` round-trips, keccak of 0/32/64-byte
  inputs), with the mandatory edge inventory: 0, 1, 2⁶⁴±1 per limb
  position, 2²⁵⁵, 2²⁵⁶−1, `sdiv smin (−1)`, every divisor-zero case,
  `signextend` k ∈ {0..31, 32, huge}, `byte` i ∈ {0..32, huge}, shifts
  s ∈ {0,1,63,64,127,128,255,256,257,huge}, `addmod/mulmod` z ∈
  {0,1,2,max}, exp exponent ∈ {0,1,2,255,256-bit} — **plus fixed-seed
  pseudorandom cases (seed recorded in the JSON header)**. A runner mode
  `elevm --u256 <file.json>` dispatches by op name **through the same
  functions and instances the interpreter uses**. Terminology discipline:
  green-on-incumbent **validates** the oracle (differential evidence); it
  is not a proof — a disagreement is a finding to diagnose against local
  EELS source, never silently resolved.
- **Existing tiers**: `scripts/check.sh --smoke/--full/--bls` against
  committed baselines; `scripts/check.sh --dir <path>` as the per-step
  TARGET gate; `scripts/check-vectors.sh` (VEC) when a precompile boundary
  is touched; `scripts/check-u256.sh` (U256) for the generated word oracle.
- **Performance instruments**: `scripts/run-bench-u256.sh <label>` compiles
  `scripts/bench-u256.lean` through standalone `lean -c` + `leanc -O2` and
  records its table. `scripts/measure-u256-offenders.sh <label>` records the
  four designated offender reports without overwriting an earlier label; use
  it at Step 1 and Step 7, where all four are required. Per-step TARGETs stay
  narrow and use `check.sh --dir` on the named fixture(s). Benchmarks have no
  committed pass/fail baseline — honest recording, before and after, same
  machine, in step reports.

## Design decisions fixed by this plan

### D1 — Cost-ordered harvest; attribution before architecture

Steps are sequenced by expected win per unit of refactoring/verification
churn, and every step's report names **which change moved which number**.
No representation work happens until Step 7's gate passes on measured
evidence. This is the inversion of the retired plan, and it is deliberate:
the retired plan paid the migration cost before collecting gains that did
not require it.

### D2 — `Nat`/GMP routing on the incumbent pairs

`mul`, `div`, `mod`, `sdiv`/`smod` magnitudes, and `exp` route through
`Nat`, exactly as `addmod`/`mulmod` already do. Guard shapes are preserved
verbatim — the semantic traps carried from the retired plan's D4: EVM
`x div 0 = 0` and `x mod 0 = 0` (never a library default),
`sdiv smin (−1) = smin`, `addmod`/`mulmod` reduce in full `Nat` before
truncation, `exp 0 0 = 1`, shift amounts ≥ 256, `byte` index ≥ 32,
`signextend` k ≥ 31 identity. The golden vectors pin all of these before
any implementation changes.

### D3 — EXP is `Nat.powMod`, directly

`B256.bexp x y := (Nat.powMod x.toNat y.toNat (2^256)).toB256`. No wrapped
square-and-multiply ladder around `U256`/pair masking, no per-round
conversions. `Nat.powMod`'s `m ≤ 1` guard is unreachable at `2^256`;
`exp = 0` returns 1 (matches EVM `0^0 = 1`) — both pinned by vectors, not
by trust. Gas (`bytecount`, `gExp`/`gExpbyte`) is untouched.

### D4 — Upstream exact-theorem ABI; downstream unfoldings die

Every routed op ships, in elevm, its `toNat` characterization in the same
step that changes the definition: `B256.toNat_toB256 : (Nat.toB256 n).toNat
= n % 2^256`, `toNat_mul : (x * y).toNat = x.toNat * y.toNat % 2^256`,
`toNat_div`, `toNat_mod`, `toNat_bexp`, with zero-divisor corollaries —
stated in elevm's own idiom (agent checks the existing `Nat` corpus,
`Basic.lean:863-1119`, before inventing forms). Blanc consumes theorems,
never definition unfoldings; its local pair-arithmetic developments are
**deleted** at integration, not ported. The name collision this creates
(blanc already declares `B256.toNat_mul` locally) is the deliberate
forcing function: the pin bump cannot compile until the local duplicate is
removed.

### D5 — Pin-bump integration protocol

The retired plan assumed `require elevm from "../elevm"`; that workflow no
longer exists. Cross-repo integration is now explicit, and only at named
integration steps (4, 7, and Phase B's 11): (i) temporarily point blanc's
`require` at the local elevm path — an uncommitted working-tree edit;
(ii) repair blanc; (iii) commit and push elevm; (iv) restore the git
`require` at the new revision, update the manifest; (v) re-verify blanc
green including the four protected theorems; (vi) commit blanc. Never
commit blanc pinned to an unpushed revision. Between integration steps,
blanc is green *by construction*.

### D6 — Decode work never touches proof-load-bearing shapes

Verified exposure: blanc's `Semantics.lean` defines its `*.At` predicates
over `getInst` and unfolds `Ninst.run` via `simp only`. Therefore the
decode optimization changes **only the implementation of `B8L.toB256`**
(same name, same type; two mapped blanc proof repairs), and the
`getInst`/`Inst`/`Ninst.run`/`exec` definitions stay byte-identical. A
pc-indexed predecode cache is sanctioned **only if** the codec fix leaves
`loopMul` red, must enter through a new function proved or
differentially-tested equal to `getInst`, and its blanc churn (it would
change `exec`, which Solvent proves against) must be costed in the report
*before* any attempt. Default expectation: the cache is not built.

### D7 — Phase B is evidence-gated, with the design corrected

Enter Phase B only if, after Phase A, Step 7's profiling shows ordinary
word ops (add/sub/compare/bitwise) remain ≥ ~20% of representative
non-pathological workload profiles **and** the flat-limb prototype
projects ≥ 10–15% end-to-end improvement — thresholds pre-registered here
so the decision cannot be vibes. If entered, Phase B carries the retired
plan's design assets with these corrections baked in:

- flat `structure B256 (l3 l2 l1 l0 : UInt64)`; `BitVec 256` is the
  **specification model only**;
- the executable `toNat` is **direct limb recombination**
  (`l3.toNat * 2^192 + …`); the model equality
  `toBitVec.toNat = toNat` is a *theorem* — runtime never routes through
  the model (the retired plan had this backwards in D2/Step 3);
- module layout settled **before** code: extract a `Bytes`/prelude module
  both `Basic` and the new `Word` import — the retired plan's
  `Basic ↔ Word` import cycle is resolved on paper, not discovered
  mid-step;
- complete inventories mandated up front: the full order-instance surface
  (`Preorder`/`PartialOrder`/`LinearOrder` etc., `Types.lean` ~639–705),
  and `Hashable` instance-by-instance (including the all-limb composite
  hash and its regression keys);
- `bv_decide` facts re-verified at entry (add/compare were verified on
  this toolchain at plan-writing time); never `bv_decide` on mul; proof
  elaboration time and `.olean` size are recorded per step.

### D8 — Scope exclusions (each a candidate for its own later plan)

Out of scope, deliberately: the **BLS/EC curve program**
(projective/Jacobian coordinates, batched inversion, structured final
exponentiation — plan-time sampling shows this is where all BLS time
lives); native backends of any kind; `Mem`/calldata `ByteArray`-ification
and MLOAD/MSTORE word paths (deferred so they are written once, against
whichever representation survives Step 7 — not twice); `List B256` stack
and container swaps; the 5 FAIL files (correctness, separate arc); **`Adr`
migration** — no arithmetic, no profile evidence; reconsidered only inside
Phase B with lookup/hash measurements in hand, default cut. The
`U256 → B256` rename question is Phase-B-internal (Step 12): the rename is
kept — permanent load-bearing `abbrev`s have bitten this project before —
but it rides at the tail, never on the critical path.

### D9 — Generated artifacts, never hand-typed

`scripts/vectors/u256.json` comes only from the committed generator;
transcribing expected values by hand is forbidden. Same for any table a
fast path needs.

## Rules for every step

1. Read the applicable `AGENTS.md` and the `lean-inspector`/`lean-prover`
   skills before touching Lean source. Use `lean-lsp-mcp` diagnostics
   during edits. Builds are end-of-step gates, never proof-state probes.
2. Inspect current definitions and references before editing. Line numbers
   and counts in this plan are plan-writing-time observations and may
   drift.
3. One step is one reviewable commit per touched repository, created by
   the user after review. Do *not* commit before the user has reviewed all
   changes manually. Suggested message family: `u256v2 : step N`.
4. Never add `sorry`, axioms, `ofReduce*`, intentionally invalid syntax,
   or a permissive fallback that converts a wrong output into a pass.
5. Blanc stays green by construction between integrations (the pin). At
   integration steps the four protected theorem statements must not
   change; repairs land in the same step.
6. Baselines are preserved byte-for-byte **except** sanctioned
   TIMEOUT → PASS flips — which are this plan's goal: a flip requires the
   timing evidence in the step report and the baseline edit in the same
   commit. Regressions are never rebased away.
7. A red U256 vector is a stop-the-line event: diagnose the op, fix,
   rerun — never adjust a vector to match the implementation. The
   generator and local EELS source are the authority; if you believe a
   *vector* is wrong, prove it against EELS source in the report before
   regenerating.
8. Performance claims come only from the committed instruments on the
   reporting machine, before/after, same machine. No vibes. Attribute
   every improvement to its step.
9. **Gate tiering** (the retired plan ran FULL+BLS nearly every step;
   that cost is not paid here): U256 + TARGET (`check.sh --dir` on the
   step's named fixtures) + SMOKE after every step; VEC only when a
   precompile boundary is touched; FULL at Steps 1, 4, 7 (and Phase B's
   11–12); BLS at Steps 1 and 7 only (nothing in Phase A touches BLS code
   paths; the Step-1/7 runs are the honesty bookends).

## Verification gates

- **V0** — `lake build` green in elevm; in blanc only at integration
  steps (elsewhere it is green by construction).
- **U256** — `elevm --u256 scripts/vectors/u256.json` fully green.
- **TARGET** — `scripts/check.sh --dir <path>` on the fixtures the step
  claims to move, with per-file wall-clocks recorded. For the four designated
  offenders together at Step 1 and Step 7, use
  `scripts/measure-u256-offenders.sh <label>` instead.
- **VEC** — `scripts/check-vectors.sh` verdicts unchanged (precompile
  steps only).
- **SMOKE / FULL / BLS** — tier verdicts against committed baselines,
  per the tiering rule; TIMEOUT flips per rule 6.
- **BENCH / TIME** — `scripts/run-bench-u256.sh <label>` records the
  micro-benchmark rows; tier wall-clocks are recorded in the step report
  (honesty instruments, no pass/fail).

Each step ends with a report in the `patch.md` style: what changed, gates
run with verdicts, timings, observations — including any evidence that
contradicts this plan.

## Model allocation per step

Same option set and placement as `precomps.md` (July 2026: Claude Code
with Fable 5 / Opus 4.8 / Sonnet 5; Codex GPT-5.4→5.6 Sol; Antigravity
Gemini 3.5 Flash / 3.1 Pro; substitute current equivalents as these age),
and the same principles: Lean 4 competence is the floor; tight gates make
under-provisioning cheap on shallow steps; two focused repair attempts,
then escalate one tier.

| Step | Difficulty | Suggested models | Rationale |
|---|---|---|---|
| 1 — oracle + instruments + baselines | ★★ | Sonnet 5 · 5.6 Terra/medium · 3.5 Flash/high (script half) | Generator/runner on an existing pattern; the validated-on-incumbent gate catches dishonesty immediately. |
| 2 — EXP via `Nat.powMod` | ★ | Sonnet 5 · 5.6 Luna/medium | A few lines, semantics-sensitive; vectors carry the risk. |
| 3 — `Nat`-route heavy family + theorem ABI | ★★☆ | Sonnet 5 · 5.6 Terra/medium | Routing is mechanical; the theorems are near-one-liners but their *statements* must match blanc's consumption idiom. |
| 4 — integration A: pin bump + blanc repair | ★★★ | Opus 4.8/medium · 5.6 Terra/high | Cross-repo; deletes a 320-line development; the risk is a hidden unfold dependency the exposure map missed. |
| 5 — decode/PUSH codec fast path | ★★☆ | Sonnet 5 · 5.6 Luna/high | Perf-sensitive codec rewrite with bounded in-repo proof repair; D6 fences the blast radius. |
| 6 — precompile inner loops | ★★★ | Sonnet 5 · 5.6 Terra/medium | Imperative-Lean loop specialization; profile-first discipline; escalate if the profiler contradicts the plan. |
| 7 — integration B + harvest + Phase-B gate | ★★☆ | Sonnet 5 (ops) + Opus 4.8/high (decision memo) | Bookkeeping plus one genuine judgment call against pre-registered thresholds. |
| 8 — module extraction | ★★ | Sonnet 5 · 3.5 Flash/high | Mechanical, cycle-safe by design. |
| 9 — U256 core + codecs + instances | ★★★ | Sonnet 5 · 5.6 Terra/medium | Carry code, differentially vector-gated the moment it exists. |
| 10 — BitVec model + proofs + blanc ABI | ★★★★ | Opus 4.8/high · 5.6 Terra/xhigh; escalate to **Fable 5** on unexpected bv_decide failure | The deep step; the reason Phase B is gated. |
| 11 — flip + integration C | ★★★☆ | Opus 4.8/medium · 5.6 Terra/high | Mechanically wide, intellectually bounded; stamina risk. |
| 12 — cleanup, rename, `Adr` decision | ★★ | Sonnet 5 · 3.5 Flash/high | Reference-checked deletions and honest bookkeeping. |

---

# Phase A — unconditional

## Step 1 — Golden op-vector oracle, instruments, attribution baselines

### Agent prompt

Work in `/Users/bsk/elevm`; change no EVM semantics. Three deliverables.

**(a) Vector generator + runner.** Write `scripts/gen-u256-vectors.py`
(plain Python 3, stdlib only): mirror the Prague EELS instruction formulas
(read them at
`~/execution-specs/src/ethereum/prague/vm/instructions/{arithmetic,comparison,bitwise,keccak}.py`
and `.../vm/gas.py` in this session; re-derive every formula from that
source) over plain ints and emit `scripts/vectors/u256.json` per the
"Correctness oracle" section: curated edge inventory **plus fixed-seed
pseudorandom cases**, with the EELS revision
(`git -C ~/execution-specs rev-parse HEAD`) and the seed recorded in the
JSON header. Format: one array of
`{"op": str, "args": [hex256…], "expected": hex256}` (comparisons emit 0/1
words; `bytecount`/`exp_gas` small ints; keccak cases carry byte strings).
Add `elevm --u256 <file>` to `Main.lean` following the `--vectors` runner
pattern: dispatch each vector by op name to the **same** `B256`
functions/instances the interpreter uses, print one line per vector, end
with the check.sh verdict-line contract. Gate: every vector green against
the *current* pair implementation — this **validates** the oracle (say
"validates", not "proves"). A disagreement with current elevm behavior is
a **finding** (latent arithmetic bug or generator bug): diagnose against
EELS source and report before changing either side.

**(b) Bench.** Commit the plan-time micro-benchmark as
`scripts/bench-u256.lean` with a header documenting the compile/run recipe
(standalone `lean -c` + `leanc -O2`; not part of the lake build) and the
forced-sequencing pitfall; run
`scripts/run-bench-u256.sh step1` once and record its table.

**(c) Baselines + exposure re-verification.** Record: both repo commits
and blanc's pin; tier wall-clock totals for SMOKE, FULL, BLS, VEC run
once, unchanged; per-file wall-clocks for the four offenders with
`scripts/measure-u256-offenders.sh step1` (it records `vmPerformance/` and
exactly the two named `stTimeConsuming` files under separate Step-1 reports).
Re-run and record the exposure-map `rg` checks from "Starting point"
(blanc references to `bexp|divMod|divOffset|mulx|B8L.toB256|Ninst.run|getInst`)
so Steps 3–5 inherit a fresh map, not this plan's snapshot. [V0 +
U256(current impl) + VEC + SMOKE + FULL + BLS + BENCH/TIME recorded]

### Note for the reader

The safety net first, exactly as in the precomps arc: op-level attribution
the blockchain fixtures cannot give. A wrong quotient after Step 3
surfaces here as `div` red, not as an opaque state-root mismatch three
layers up. The oracle is *validated* against the incumbent before any new
code exists; from Step 2 on, every red is attributable to that step's
change.

---

## Step 2 — EXP: `Nat.powMod`, the highest leverage-per-line change

### Agent prompt

In `Basic.lean`: replace the body of `B256.bexp` with
`(Nat.powMod x.toNat y.toNat (2 ^ 256)).toB256`; delete `bexpCore` (check
in-repo references first — `teg` stays, it is general bit access). Keep
the name, type, and `HPow` instance; `bytecount` and the gas path
(`gExp`/`gExpbyte`, `Execution.lean:594,626-627`) are untouched. Confirm
against the exp-family vectors that the edge semantics hold: `0^0 = 1`,
base 0/1, exponent 0/1/255/full-256-bit, and that `Nat.powMod`'s `m ≤ 1`
guard is unreachable. Run TARGET on `vmPerformance/`: `loopExp.json` is
expected to flip TIMEOUT → PASS — if it does, edit `baseline-full.txt`
(and any other tier listing it) in the same commit with the timing in the
report; if it does not, record the new wall-clock and profile before
touching anything else. [U256 + TARGET(vmPerformance) + SMOKE +
BENCH(exp row)]

### Note for the reader

~5 lines replacing ~512 pair-multiplications per EXP with one GMP modular
exponentiation. Zero blanc exposure (verified: `bexp` is applied, never
unfolded, downstream). This step is deliberately alone: it is the
proof-of-pattern for D2, and its before/after is the cleanest attribution
datum the whole arc will produce.

---

## Step 3 — `Nat`-route the heavy family + upstream theorem ABI

### Agent prompt

In `Basic.lean`, on the unchanged pair type: (a) `B256.mul x y :=
(x.toNat * y.toNat).toB256`; (b) `B256.divMod x y := if y = 0 then ⟨0, 0⟩
else ⟨(x.toNat / y.toNat).toB256, (x.toNat % y.toNat).toB256⟩` — guard
shape preserved; (c) `sdiv`/`smod` keep their current case/guard structure
(`Basic.lean:537-554`, including `smin`/`negOne` handling), routing only
the magnitudes through `Nat`. Delete `divOffset`/`divModCore` and the
`mulx` chains **iff** in-repo references are empty (`rg` +
`lean_references`; blanc's `mulx` references live only in the Solvent
development scheduled for deletion next step — expected and intended).
(d) Ship the theorem ABI in the same commit:
`B256.toNat_toB256 : (Nat.toB256 n).toNat = n % 2^256`, `toNat_mul`,
`toNat_div`, `toNat_mod`, `toNat_bexp`, with divisor-zero corollaries —
statements in elevm's idiom after checking the existing `Nat` corpus
(`Basic.lean:863-1119`) for the forms already in use. Sanctioned optional:
mask-based `signext` (drop the 32-byte list) — take it only if the vector
family is already green and time remains; otherwise note-and-skip.
Measure the mul delta honestly (BENCH row): the pair-conversion overhead
means the win is expected ~2–4×, not the table's 6×. [U256 +
TARGET(vmPerformance + one arithmetic-heavy `--dir` named in the report) +
SMOKE + BENCH(mul/div rows)]

### Note for the reader

After this step no O(bits) loop remains in the interpreter's word
arithmetic; everything heavy is one GMP call behind the existing guards.
The theorem ABI shipped here is what makes Step 4 net-negative: blanc's
320-line development exists *because* upstream never exported
`toNat_mul`. The deliberate name collision (D4) means Step 4 cannot
silently keep both.

---

## Step 4 — Integration point A: pin bump + blanc repair (net-negative)

### Agent prompt

Execute the D5 protocol. Expected blanc repairs, pre-mapped: delete
`Solvent.lean` ~6843–7166 (`B64.toNat_mulx`, `B128.toNat_mulx`, the local
`B256.toNat_mul`, and their carry helpers — the upstream lemma now
collides with the local declaration, so the build forces this); adapt the
single consumer (`Solvent.lean:7196`,
`processWithdrawalsState_inv_solvent`) to the upstream statement — the
`↾ 256` vs `% 2^256` idiom gap bridges via blanc's `Nat.lo` lemmas
(`Nat.lo_eq_of_lt` is already in the proof) in ~2 lines. Before editing,
re-run the exposure map from Step 1(c) against the *new* elevm to catch
any unfold dependency this plan missed; more breakage than mapped is a
stop-and-re-map signal, not an improvisation license. The four protected
theorem statements must not change; finish with `lean_verify` on all four.
[V0 both repos + U256 + SMOKE + FULL + protected theorems verified]

### Note for the reader

The first cross-repo touch, and the step that demonstrates the
verification claim of the whole algorithms-first ordering: ~320 proof
lines deleted, ~5 added, four theorems intact. If the exposure map holds,
this is a half-session; the provisioning above is for the case it does
not.

---

## Step 5 — Decode/PUSH codec fast path (the loopMul attack)

### Agent prompt

Within the D6 fence — `getInst`, `Inst`, `Ninst.run`, `exec` byte-
identical: rewrite `B8L.toB256` (`Basic.lean:1228-1233`) as a single
left-to-right pass assembling the four 64-bit halves directly from the
byte list (no `pack`, no `take`/`drop`, no intermediate reversals),
preserving big-endian semantics and the ≤32-byte zero-extension behavior
exactly (the codec vectors pin this). Repair the bounded in-repo proof
surface (`B8L.toB256?`, round-trip lemmas near `Basic.lean:1226+`) —
prefer proving the new definition equal to the old shape once and
rewriting through it. Note for the Step-7 integration: blanc unfolds this
definition in exactly two proofs (`Common.lean:1315-1318`, `:6766`);
pre-stage the equation lemma they will need. Then measure: TARGET on
`vmPerformance/` (loopMul), plus a BENCH row for the codec itself.
CALLDATALOAD (`Execution.lean:2191`) benefits with zero extra edits. If
`loopMul` remains TIMEOUT: record the fresh profile, cost the predecode
cache per D6 (it would modify `exec`, which blanc's Solvent proves
against), and **stop** — the decision to pay that churn is the user's,
made on the report, not the agent's. Sanctioned split: 5a = codec rewrite
+ in-repo repair; 5b = (only if sanctioned after the report) the cache.
[U256 + TARGET(vmPerformance) + SMOKE + BENCH(codec row)]

### Note for the reader

Plan-time sampling says loopMul's time is decode churn, not
multiplication — this step is the minimal-churn test of that attribution.
The expensive alternative is named, fenced, and default-rejected in D6;
if the cheap fix flips the fixture, the fence never gets tested.

---

## Step 6 — Precompile inner loops: Blake2F, SHA-256 (cuttable)

### Agent prompt

Profile before touching: sample `static_Call50000_sha256.json` (the one
offender with no plan-time attribution) and re-sample `CALLBlake2f_
MaxRounds.json`; record both in the report. Then, guided by the profiles:
(a) specialize the Blake2 compression loop (`Blake2.g` and its driver,
`Execution.lean:3043-3105`) — monomorphic, minimal bounds-checked
indexing, no higher-order round plumbing, state in a shape the compiler
keeps unboxed as far as Lean allows; (b) same treatment for `SHA256.run`
(`Hash.lean:125-263`) if and only if the profile says the SHA loop
dominates. Byte-for-byte output equality is gated by VEC (blake2F/sha
vectors) and the fixture suite. Expectations registered now: the sha file
is a plausible flip; `CALLBlake2f_MaxRounds` may **not** flip — at
~2³² rounds even a several-fold constant factor can leave it over 100 s;
the honest deliverable there is the measured factor and the verdict, not
a forced flip. Zero blanc exposure (verified: blanc references keccak
only). Sanctioned split: 6a = Blake2F; 6b = SHA. [U256 + VEC +
TARGET(the two stTimeConsuming files) + SMOKE + BENCH(per-loop rows)]

### Note for the reader

Contained, proof-free, vector-gated, and severable: cutting this step
forfeits nothing downstream. It exists because two of the four visible
timeouts live here and nowhere near `B256` — the clearest illustration of
why attribution precedes architecture.

---

## Step 7 — Integration point B, harvest A, and the Phase-B gate

### Agent prompt

Three parts. **(a) Integration**: D5 protocol for the Steps 5–6 elevm
changes; pre-mapped blanc repairs: the two `B8L.toB256` unfolding proofs
(`Common.lean:1315-1318`, `:6766`) via the Step-5 equation lemma; verify
the four theorems. **(b) Harvest**: re-run every instrument — bench table,
all tier wall-clocks including BLS, per-offender timings via
`scripts/measure-u256-offenders.sh step7` — and produce the before/after
comparison against Step 1, with each delta
attributed to its step; audit every TIMEOUT classification and flip only
with evidence (rule 6). **(c) The gate**: profile representative
*non-pathological* workloads (name ≥3 fixture families from FULL in the
report, e.g. arithmetic- and memory-heavy directories) and measure the
share of time in ordinary word ops (add/sub/compare/bitwise). Write the
go/no-go memo against D7's pre-registered thresholds (word ops ≥ ~20% of
profile; projected ≥ 10–15% end-to-end). **No-go**: close the plan —
Phase A stands as a complete banked win; the report restates D8's
exclusions as the natural follow-on plans (BLS curve program first if
vector throughput matters, byte/`ByteArray` layer, containers) and
archives the Phase-B design for when conditions change. **Go**: the
memo's numbers become Phase B's baseline; proceed. [V0 both repos + U256 +
VEC + SMOKE + FULL + BLS + BENCH/TIME final-for-phase + protected
theorems verified]

### Note for the reader

The honest fork in the road, and the step the critique demanded: the
representation migration gets built on measured residual need or not at
all. Either verdict is a success for this plan; only an unmeasured
verdict is a failure.

---

# Phase B — conditional on Step 7's gate

The retired plan's Steps 2–8, restructured to remove its verified defects
(import cycle, model-in-runtime `toNat`, missing order/hash inventories,
oversized sessions) and to inherit Phase A's assets (the oracle, the
theorem ABI, the pin protocol). Prompts are deliberately leaner: if the
gate passes, the executing agent re-derives fresh line numbers from
Step 7's report before starting, and the Step-10 family splits are
mandatory, not sanctioned.

## Step 8 — Module extraction (cycle-safe layout)

**Agent prompt.** In elevm, extract the width-independent prelude both
`Basic` and the future `Word` module need — `B8`/…/`B64` abbrevs, byte-list
helpers, the `Nat` helper corpus — into `Elevm/Bytes.lean` (or split
`WordCore`/`WordCodec` if elaboration argues for it), with **zero behavior
change** and the import DAG written down in the step report before any
code moves. [V0 + U256 + SMOKE]

**Note.** The retired plan discovered its `Basic ↔ Word` cycle nowhere;
this plan discovers it here, on paper, for the cost of one mechanical
session.

## Step 9 — U256 core, codecs, instances (family splits sanctioned)

**Agent prompt.** `Elevm/Word.lean`: `structure U256 (l3 l2 l1 l0 :
UInt64)` with the native limb ops (add/sub/neg/not/and/or/xor, unsigned
and signed comparisons, shl/shr/sar by `Nat`, byte, signext, iszero,
bytecount, min/max), the `Nat`-routed ops delegating to the Phase-A
algorithms, **executable `toNat` by direct limb recombination**, codecs
byte-compatible with the current big-endian layout, and the *complete*
instance surface from the Step-7-refreshed inventory: every `H*` op
instance, `Ord`/`compare`, the full order tower
(`Preorder`/`PartialOrder`/`LinearOrder`), `Hashable` instance-by-instance
(all-limb composite hash + regression keys preserved), `Inhabited`,
`OfNat`, constants. Extend `--u256` with the `--diff` mode: every vector
through old and new ops, failing on divergence. No consumer changes.
Splits: representation+conversions / add-sub-bits-compare /
shifts-signed-byte-signext / codecs+instances. [V0 + U256(old) +
U256-diff(new) + SMOKE]

## Step 10 — `BitVec` model, op proofs, blanc ABI (the deep step)

**Agent prompt.** `U256.toBitVec` by limb append; theorem
`toBitVec_toNat : x.toBitVec.toNat = x.toNat` (the model is never the
definition); one correctness lemma per op against the model — `bv_decide`
where verified (add, compare; lift through `UInt64.toBitVec_*`), bounded
case analysis for symbolic-`Nat` shifts, round-trip + `toNat` algebra for
`Nat`-routed ops, never `bv_decide` on mul. Then restate the blanc-facing
ABI (the `toNat_*`/`Nof`/`le_iff…`/`lt_check`/codec names from the
refreshed inventory) statement-equivalent on the model. Record proof
elaboration time and `.olean` size per family; a proof layer that
kernel-checks but doubles rebuild time is a reported cost, not a silent
one. Mandatory splits: model foundations / native families /
shifts-signed / Nat-routed+codecs / ABI restatement. [V0 + U256 gates +
inventory checklist]

## Step 11 — The flip + integration point C

**Agent prompt.** `abbrev B256 := U256` in `Basic.lean`; delete the pair
op layer; repair the structural sites (codecs/hex, `Types.lean`
`toAdr`/`toB256` bridge, `Hash.lean` keccak collapse, `Main.lean`
parsers, `EC.lean` ecrecover plumbing); `Execution.lean` is expected to
compile with near-zero edits — treat any exception as a missing Step-9
API, not a call-site problem. Then the D5 pin protocol and blanc's
structural repair (the `Solvent.lean` 401–476 mask family and whatever
the refreshed inventory flagged). Four theorem statements unchanged.
Split: elevm flip / blanc repair — blanc may be red in the working tree
between them; commits only when every gate is green. [V0 both + U256 +
U256-diff retired (final run recorded) + VEC + SMOKE + FULL + BLS +
BENCH/TIME]

## Step 12 — Cleanup, rename, `Adr` decision, closure

**Agent prompt.** Reference-checked deletions across both repos
(`lean_references` + `rg`); the `U256 → B256` rename (kept per D8's
rationale — this project has been bitten by permanent load-bearing
abbrevs — but executed here at the tail, mechanically, type-checked);
the `Adr` decision made on measurement: profile account-map
compare/hash cost, and migrate `Adr` only if it registers — otherwise
record the cut with the numbers. Final report: full gate matrix,
Phase A + B performance tables with per-step attribution, an explicit
statement of what changed and what did not (D8 restated as follow-on
plans), and every piece of evidence gathered that should revise those
plans' priors. [V0 + U256 + VEC + SMOKE + FULL + BLS + BENCH/TIME final]

---

## End condition

Phase A alone: same green fixture matrix modulo evidenced TIMEOUT → PASS
flips (loopExp expected, loopMul and sha plausible, Blake2F honest-effort),
the same four blanc theorems, ~320 lines of downstream proof deleted, and
an interpreter whose word arithmetic has no O(bits) loops — all without
changing a single type. Phase B, if and only if the numbers demand it:
the flat-limb representation with a `BitVec` model, landed on a proof
budget that was measured, not guessed. Either way, the follow-on plans
(BLS curve program, byte layer, containers) start from this arc's
recorded profiles rather than from intuition.
