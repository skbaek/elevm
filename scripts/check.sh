#!/usr/bin/env bash
# Fixture-test harness for elevm (REFACTOR.md Phase 0, step 0.1).
#
# Usage: scripts/check.sh (--depth | --smoke | --full | --patch | --rlp4 | --bls | --dir <path>) [--report <path>] [--rebase] [--no-build]
#
#   --depth       run the fuel/call-depth stress set (scripts/depth-tests.txt)
#   --smoke       run the smoke set (scripts/smoke-tests.txt)
#   --full        run every .json fixture under the fixture root
#   --patch       run the patch-plan target set (scripts/patch-tests.txt): the
#                 ten historical FAIL files
#   --rlp4        run the four invalid-RLP/header files (scripts/rlp4-tests.txt),
#                 a subset of --patch
#   --bls         run the EEST consensus set for the BLS12-381 and
#                 point-evaluation precompiles (scripts/bls-tests.txt) against
#                 the committed hand-authored target baseline
#                 scripts/baseline-bls.txt (precomps.md Step 9); the fixture
#                 root and per-file timeout defaults differ — see Environment
#   --dir <path>  run one .json fixture, or every .json fixture under a
#                 directory (the path must be inside the fixture root); ad hoc
#                 — if no baseline-dir.txt exists, the gate passes iff every
#                 selected file PASSes
#   --report <p>  write this run's report to <p> instead of overwriting the
#                 default scripts/report-<tier>.txt
#   --rebase      accept the current results as the new committed baseline
#                 (rejected for --patch/--rlp4: their desired result is fixed)
#   --no-build    skip `lake build elevm`
#
# --patch and --rlp4 are target gates, not baseline-comparison tiers: each
# succeeds if and only if every listed file is PASS. They have no baseline and
# never rebase. Their reports additionally record per-file elapsed wall time.
# Ad-hoc --dir reports also record elapsed time for performance measurements.
#
# --bls compares against a committed baseline like the ordinary tiers, but the
# baseline is a hand-authored target (all PASS unless an entry carries a
# written justification), so --rebase is rejected; edit baseline-bls.txt
# directly instead. `#` comment lines in it document exclusions and
# justifications. Like the target gates, its report records wall times.
#
# Environment:
#   ELEVM_FIXTURES  fixture root (default:
#                   ~/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests;
#                   for --bls: ~/eest-fixtures/fixtures/blockchain_tests, the
#                   pinned EEST release snapshot — see scripts/vectors/SOURCES.md)
#   ELEVM_TIMEOUT   per-file timeout in seconds (default: 100; for --bls: 1200,
#                   sized for the EEST stress files — 46 MB test_valid.json and
#                   the 122-case KZG external-vector file)
#
# A failing test makes elevm throw and abort the whole invocation, so each
# fixture file runs in its own process, under a perl-alarm timeout (macOS has
# no coreutils timeout). Per-file classification PASS / FAIL / TIMEOUT is
# written to scripts/report-<tier>.txt (gitignored). The gate passes iff every
# file's classification equals the committed scripts/baseline-<tier>.txt —
# NOT iff every file passes. A PASS/FAIL change is a functional regression.
# A change involving TIMEOUT is environment/performance-sensitive, so it is
# reported separately as REVIEW rather than asserted to be a regression.
#
# CLI contract: exit 0 if and only if the gate passes; the last line of
# output is a single unambiguous verdict line.

set -u

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/elevm"

usage() {
  echo "usage: scripts/check.sh (--depth | --smoke | --full | --patch | --rlp4 | --bls | --dir <path>) [--report <path>] [--rebase] [--no-build]" >&2
  exit 2
}

TIER=""
DIR_PATH=""
REBASE=0
BUILD=1
REPORT_PATH=""
while [ $# -gt 0 ]; do
  case "$1" in
    --depth|--smoke|--full|--patch|--rlp4|--bls) TIER="${1#--}" ;;
    --dir)
      TIER="dir"
      shift
      [ $# -gt 0 ] || usage
      DIR_PATH="$1"
      ;;
    --report)
      shift
      [ $# -gt 0 ] || usage
      REPORT_PATH="$1"
      ;;
    --rebase) REBASE=1 ;;
    --no-build) BUILD=0 ;;
    *) echo "unknown argument: $1" >&2; usage ;;
  esac
  shift
done
[ -n "$TIER" ] || usage

# Tier-dependent defaults: the bls tier runs the pinned EEST release snapshot,
# which lives outside the default fixture root, and its stress files (46 MB
# test_valid.json at ~265-285 s, the 122-case KZG external-vector file at
# ~109 s) need a larger per-file timeout than the legacy tiers' 100 s.
if [ "$TIER" = "bls" ]; then
  FIXTURES="${ELEVM_FIXTURES:-$HOME/eest-fixtures/fixtures/blockchain_tests}"
  TIMEOUT="${ELEVM_TIMEOUT:-1200}"
else
  FIXTURES="${ELEVM_FIXTURES:-$HOME/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests}"
  TIMEOUT="${ELEVM_TIMEOUT:-100}"
fi

# Target-gate tiers succeed iff every listed file is PASS; they have no
# baseline and never rebase.
case "$TIER" in
  patch|rlp4) IS_TARGET=1 ;;
  *)          IS_TARGET=0 ;;
esac
if [ "$IS_TARGET" -eq 1 ] && [ "$REBASE" -eq 1 ]; then
  echo "usage error: --rebase is not supported for the $TIER target gate; its desired result is fixed at all-PASS" >&2
  exit 2
fi

# The bls tier compares against a committed hand-authored target baseline;
# accepting observed results wholesale would defeat it.
if [ "$TIER" = "bls" ] && [ "$REBASE" -eq 1 ]; then
  echo "usage error: --rebase is not supported for the bls tier; its baseline is a hand-maintained target — edit scripts/baseline-bls.txt directly" >&2
  exit 2
fi

if [ ! -d "$FIXTURES" ]; then
  echo "REGRESSION — $TIER: fixture root not found: $FIXTURES"
  exit 1
fi

# Assemble the file list (paths relative to the fixture root, sorted).
case "$TIER" in
  depth|smoke|patch|rlp4|bls)
    LIST_FILE="$SCRIPT_DIR/$TIER-tests.txt"
    if [ ! -f "$LIST_FILE" ]; then
      echo "REGRESSION — $TIER: file list not found: $LIST_FILE"
      exit 1
    fi
    FILES="$(grep -v '^[[:space:]]*$' "$LIST_FILE")"
    ;;
  full)
    # .meta/ holds fixture-index metadata, not tests.
    FILES="$(find "$FIXTURES" -name '*.json' | sed "s|^$FIXTURES/||" \
      | grep -v -e '^\.meta/' -e '/\.meta/' | sort)"
    ;;
  dir)
    if [ ! -e "$DIR_PATH" ]; then
      echo "REGRESSION — dir: path not found: $DIR_PATH"
      exit 1
    fi
    if [ -d "$DIR_PATH" ]; then
      ABS="$(cd "$DIR_PATH" && pwd)"
    elif [ -f "$DIR_PATH" ]; then
      ABS="$(cd "$(dirname "$DIR_PATH")" && pwd)/$(basename "$DIR_PATH")"
      case "$ABS" in
        *.json) : ;;
        *) echo "REGRESSION — dir: selected file is not JSON: $ABS"; exit 1 ;;
      esac
    else
      echo "REGRESSION — dir: path is not a regular file or directory: $DIR_PATH"
      exit 1
    fi
    case "$ABS" in
      "$FIXTURES"|"$FIXTURES"/*) : ;;
      *)
        echo "REGRESSION — dir: $ABS is not under the fixture root $FIXTURES"
        exit 1
        ;;
    esac
    if [ -d "$ABS" ]; then
      FILES="$(find "$ABS" -name '*.json' | sed "s|^$FIXTURES/||" | sort)"
    else
      FILES="${ABS#"$FIXTURES"/}"
    fi
    ;;
esac

TOTAL="$(printf '%s\n' "$FILES" | grep -c .)"
if [ "$TOTAL" -eq 0 ]; then
  echo "REGRESSION — $TIER: no fixture files selected"
  exit 1
fi

if [ "$BUILD" -eq 1 ]; then
  if ! (cd "$ROOT" && lake build elevm); then
    echo "REGRESSION — $TIER: lake build elevm failed"
    exit 1
  fi
fi
if [ ! -x "$BIN" ]; then
  echo "REGRESSION — $TIER: elevm binary not found: $BIN"
  exit 1
fi

REPORT="${REPORT_PATH:-$SCRIPT_DIR/report-$TIER.txt}"
BASELINE="$SCRIPT_DIR/baseline-$TIER.txt"
mkdir -p "$(dirname "$REPORT")"
: > "$REPORT"

NPASS=0
NFAIL=0
NTIMEOUT=0
I=0
while IFS= read -r REL; do
  [ -n "$REL" ] || continue
  I=$((I + 1))
  START="$(perl -MTime::HiRes=time -e 'printf "%.3f", time')"
  # alarm(2) persists across exec: when the timeout fires, SIGALRM kills the
  # exec'd elevm (exit status 128 + 14 = 142).
  perl -e 'alarm shift @ARGV; exec @ARGV' "$TIMEOUT" "$BIN" "$FIXTURES/$REL" \
    --network Prague \
    > /dev/null 2>&1
  RC=$?
  ELAPSED="$(perl -e 'printf "%.2f", $ARGV[1] - $ARGV[0]' \
    "$START" "$(perl -MTime::HiRes=time -e 'printf "%.3f", time')")"
  if [ "$RC" -eq 0 ]; then
    CLS=PASS; NPASS=$((NPASS + 1))
  elif [ "$RC" -eq 142 ]; then
    CLS=TIMEOUT; NTIMEOUT=$((NTIMEOUT + 1))
  else
    CLS=FAIL; NFAIL=$((NFAIL + 1))
  fi
  if [ "$IS_TARGET" -eq 1 ] || [ "$TIER" = "bls" ] || [ "$TIER" = "dir" ]; then
    printf '%s\t%ss\t%s\n' "$CLS" "$ELAPSED" "$REL" >> "$REPORT"
    printf '[%d/%d] %s %ss %s\n' "$I" "$TOTAL" "$CLS" "$ELAPSED" "$REL" >&2
  else
    printf '%s\t%s\n' "$CLS" "$REL" >> "$REPORT"
    printf '[%d/%d] %s %s\n' "$I" "$TOTAL" "$CLS" "$REL" >&2
  fi
done <<EOF
$FILES
EOF

SUMMARY="$NPASS PASS, $NFAIL FAIL, $NTIMEOUT TIMEOUT"

# Target gates: fixed all-PASS end condition, no baseline, no rebase.
if [ "$IS_TARGET" -eq 1 ]; then
  if [ "$NFAIL" -eq 0 ] && [ "$NTIMEOUT" -eq 0 ]; then
    echo "OK — $TIER: $NPASS/$TOTAL PASS ($SUMMARY)"
    exit 0
  fi
  echo "RED — $TIER: $NPASS/$TOTAL PASS, target not met ($SUMMARY); see $REPORT"
  exit 1
fi

if [ "$REBASE" -eq 1 ]; then
  if [ "$TIER" = "dir" ]; then
    cut -f1,3 "$REPORT" > "$BASELINE"
  else
    cp "$REPORT" "$BASELINE"
  fi
  echo "OK — $TIER: baseline rebased with $TOTAL files ($SUMMARY)"
  exit 0
fi

# The bls baseline is hand-authored (`#` comments carry exclusions and
# justifications) and the bls report carries an elapsed column; normalize
# both into the plain CLS<TAB>REL shape for the generic comparison below.
CMP_BASELINE="$BASELINE"
CMP_REPORT="$REPORT"
if [ "$TIER" = "bls" ]; then
  if [ ! -f "$BASELINE" ]; then
    echo "REGRESSION — bls: no target baseline at $BASELINE (it is committed and hand-maintained, never rebased)"
    exit 1
  fi
  CMP_DIR="$(mktemp -d)"
  grep -v -e '^[[:space:]]*#' -e '^[[:space:]]*$' "$BASELINE" > "$CMP_DIR/baseline"
  cut -f1,3 "$REPORT" > "$CMP_DIR/report"
  CMP_BASELINE="$CMP_DIR/baseline"
  CMP_REPORT="$CMP_DIR/report"
elif [ "$TIER" = "dir" ]; then
  CMP_DIR="$(mktemp -d)"
  cut -f1,3 "$REPORT" > "$CMP_DIR/report"
  CMP_REPORT="$CMP_DIR/report"
fi

if [ ! -f "$BASELINE" ]; then
  if [ "$TIER" = "dir" ]; then
    if [ "$NFAIL" -eq 0 ] && [ "$NTIMEOUT" -eq 0 ]; then
      echo "OK — dir: $TOTAL files, all PASS, no baseline ($SUMMARY)"
      exit 0
    fi
    echo "REGRESSION — dir: $NFAIL FAIL / $NTIMEOUT TIMEOUT with no baseline; see $REPORT"
    exit 1
  fi
  echo "REGRESSION — $TIER: no baseline at $BASELINE (run once with --rebase)"
  exit 1
fi

CHANGES="$(awk -F'\t' '
  NR == FNR { base[$2] = $1; next }
  {
    old = ($2 in base) ? base[$2] : "MISSING"
    if (old != $1) {
      kind = (old == "TIMEOUT" || $1 == "TIMEOUT") ? "TIMEOUT" : "FUNCTIONAL"
      print kind "\t" old "\t" $1 "\t" $2
    }
    delete base[$2]
  }
  END {
    for (file in base) {
      kind = (base[file] == "TIMEOUT") ? "TIMEOUT" : "FUNCTIONAL"
      print kind "\t" base[file] "\tMISSING\t" file
    }
  }
' "$CMP_BASELINE" "$CMP_REPORT")"

if [ -z "$CHANGES" ]; then
  NCHANGED=0
  NFUNCTIONAL=0
  NTIMEOUT_CHANGED=0
else
  NCHANGED="$(printf '%s\n' "$CHANGES" | grep -c .)"
  NFUNCTIONAL="$(printf '%s\n' "$CHANGES" | grep -c '^FUNCTIONAL')"
  NTIMEOUT_CHANGED="$(printf '%s\n' "$CHANGES" | grep -c '^TIMEOUT')"

  printf '%s\n' "$CHANGES" | while IFS="$(printf '\t')" read -r KIND OLD NEW REL; do
    if [ "$KIND" = "TIMEOUT" ]; then
      printf 'REVIEW — %s: %s -> %s (timeout-sensitive; may reflect machine load or performance)\n' \
        "$REL" "$OLD" "$NEW"
    else
      printf 'CHANGE — %s: %s -> %s\n' "$REL" "$OLD" "$NEW"
    fi
  done
fi

if [ "$NCHANGED" -eq 0 ]; then
  echo "OK — $TIER: $TOTAL files match baseline ($SUMMARY)"
  exit 0
fi
if [ "$NFUNCTIONAL" -gt 0 ]; then
  if [ "$NTIMEOUT_CHANGED" -gt 0 ]; then
    echo "REGRESSION — $NFUNCTIONAL functional classification changes; additionally $NTIMEOUT_CHANGED timeout-sensitive changes need review; see $REPORT"
  else
    echo "REGRESSION — $NFUNCTIONAL functional classification changes vs baseline; see $REPORT"
  fi
  exit 1
fi
echo "REVIEW — $NTIMEOUT_CHANGED timeout-sensitive classification changes; not definitive regressions, inspect machine load/performance and $REPORT"
exit 1
