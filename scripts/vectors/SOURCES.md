# Pinned sources for compact MSM vectors and EEST fixtures

The external-source facts on this page (execution-specs, ethereum/tests,
LegacyTests, and EEST) are also recorded machine-readably in
[`scripts/sources.json`](../sources.json), the single manifest that later
bootstrap tooling and generators are expected to consume rather than
duplicating these literals. [`scripts/env_doctor.py`](../env_doctor.py) is a
read-only, Python-standard-library-only diagnostic that checks the current
checkouts, the EEST archive/extraction, and the Python oracle venv against
that manifest; it never downloads, clones, installs, or repairs anything.
Run it with `python3 scripts/env_doctor.py` (add `--json` for machine-readable
output); pass `--execution-specs`, `--eest-root`, or `--venv` to point it at
non-default locations, or `--manifest` to check against a different manifest
file entirely. Its `EEST_ROOT` override is a doctor-specific variable naming
the top-level EEST install directory (containing the archive and its
extracted `fixtures/` tree); it is distinct from `scripts/check.sh`'s
`ELEVM_FIXTURES`, which instead points directly at a tier's leaf fixture
directory.

## Legacy fixture Git bootstrap

[`scripts/bootstrap_legacy.py`](../bootstrap_legacy.py) safely creates the
Git-backed sources used by the ordinary fixture tiers:

1. execution-specs, detached at the manifest commit;
2. the ignored, independent `tests/fixtures/ethereum_tests` checkout, detached
   at its manifest commit; and
3. only that checkout's required `LegacyTests` submodule, at the manifest
   gitlink commit.

Preview a fresh install without network or filesystem changes:

```sh
python3 scripts/bootstrap_legacy.py --dry-run
```

Install to the compatible default `~/execution-specs`, or select another
destination explicitly:

```sh
python3 scripts/bootstrap_legacy.py
python3 scripts/bootstrap_legacy.py --execution-specs "/path/with spaces/execution-specs"
EELS_ROOT="/another/path/execution-specs" python3 scripts/bootstrap_legacy.py
```

`--execution-specs` takes precedence over `EELS_ROOT`; otherwise the
manifest's home-relative default is used. The current known-good installation
occupies about 5.9 GB. Allow at least 7 GB of free space in the destination
filesystem and expect several gigabytes of public GitHub network transfer;
actual transfer size and duration depend on Git and server compression. The
bootstrap does not install Python packages or EEST fixtures.

The command builds a missing destination in a temporary sibling, verifies all
three repositories, and then places it atomically where the filesystem
supports an ordinary sibling rename. A fully correct existing installation is
an offline no-op. Any other existing target—empty, nonempty, partial, dirty,
at the wrong revision, or using an unexpected origin—is refused without
repair or overwrite.

After an interrupted process, the final destination is either absent or was
already fully placed. Inspect any sibling named
`.execution-specs.bootstrap-*` before removing it manually. For a refused
destination, inspect it and either move/remove it yourself only when certain
it is disposable, or choose a different `--execution-specs` path; the command
intentionally has no force/repair mode. Verify the finished environment with:

```sh
python3 scripts/env_doctor.py --legacy-only \
  --execution-specs "/path/to/execution-specs"
```

Omit `--legacy-only` to also diagnose the EEST and Python components handled
by later portability steps.

The test harness's existing `ELEVM_FIXTURES` override is unchanged and points
directly to `BlockchainTests`, not to the execution-specs root.

## EEST blockchain fixtures (Step 9, `--bls` tier)

The `--bls` tier of `scripts/check.sh` runs EEST consensus fixtures that are
too large to vendor. They come from one pinned execution-spec-tests fixture
release, unpacked outside the repo at `~/eest-fixtures/fixtures/`:

| Release tag | File | SHA-256 |
| --- | --- | --- |
| [`v5.4.0`](https://github.com/ethereum/execution-spec-tests/releases/tag/v5.4.0) | `fixtures_stable.tar.gz` | `92cf1b47ad12fb27163261fc3c1cea5df72439cab507983d06b56c94f8741909` |

The tier reads `blockchain_tests/prague/eip2537_bls_12_381_precompiles/` and
the point-evaluation files under `blockchain_tests/cancun/eip4844_blobs/`
(their cases are regenerated per network; the tier selects the Prague ones).

The four committed `*.head.json` files contain the first 32 entries of their
full upstream vectors. Regenerate them with the committed `jq '.[0:32]'`
commands in `scripts/check-vectors.sh`; do not hand-edit them.

## BLS constants generator

`Elevm/BLSConst.lean` is generated from the following pinned local sources:

- execution-specs commit
  [`4198b9c5996713b268aed602739d5aa40e277694`](https://github.com/ethereum/execution-specs/tree/4198b9c5996713b268aed602739d5aa40e277694)
- `py-ecc` version `8.0.0`, installed in that checkout's venv

The generator does not clone repositories or install dependencies. Point it at
an existing checkout; it verifies both pins before producing output:

```sh
~/execution-specs/venv/bin/python scripts/gen-bls-consts.py \
  --execution-specs ~/execution-specs > Elevm/BLSConst.lean
```

`EELS_ROOT` may be used instead of the command-line option. To verify the
committed constants without replacing them:

```sh
~/execution-specs/venv/bin/python scripts/gen-bls-consts.py \
  --execution-specs ~/execution-specs > /tmp/BLSConst.lean
cmp /tmp/BLSConst.lean Elevm/BLSConst.lean
```

## EIP-2537 vectors

Source commit: [`c6842c8115013524f5955d410c24e1748a615d07`](https://github.com/ethereum/EIPs/tree/c6842c8115013524f5955d410c24e1748a615d07)

| Full source | SHA-256 | Committed sample |
| --- | --- | --- |
| [`msm_G1_bls.json`](https://raw.githubusercontent.com/ethereum/EIPs/c6842c8115013524f5955d410c24e1748a615d07/assets/eip-2537/msm_G1_bls.json) | `9473ca855509a10238388355093e092fab46d80753e72a64b8c1accba8364f65` | `msm_G1_bls.head.json` |
| [`msm_G2_bls.json`](https://raw.githubusercontent.com/ethereum/EIPs/c6842c8115013524f5955d410c24e1748a615d07/assets/eip-2537/msm_G2_bls.json) | `198411e8e72830245866ad94e2f743fa2499ffb928ca7c2bd10a18ed842368ef` | `msm_G2_bls.head.json` |

## go-ethereum vectors

These two vectors are also multi-megabyte, so they follow the same compact
sample policy rather than being committed in full.

Source commit: [`06b23b4293950d8c08b624b90f310d1e918048e8`](https://github.com/ethereum/go-ethereum/tree/06b23b4293950d8c08b624b90f310d1e918048e8)

| Full source | SHA-256 | Committed sample |
| --- | --- | --- |
| [`blsG1MultiExp.json`](https://raw.githubusercontent.com/ethereum/go-ethereum/06b23b4293950d8c08b624b90f310d1e918048e8/core/vm/testdata/precompiles/blsG1MultiExp.json) | `b2603f681b9695e6ceb3cc7562c3c922b6db709882c26e84050774c0db7ce33a` | `blsG1MultiExp.head.json` |
| [`blsG2MultiExp.json`](https://raw.githubusercontent.com/ethereum/go-ethereum/06b23b4293950d8c08b624b90f310d1e918048e8/core/vm/testdata/precompiles/blsG2MultiExp.json) | `f9b3fabe719b89883be935d7482805ac1fe734419e5ec77707dc262b0fdad926` | `blsG2MultiExp.head.json` |
