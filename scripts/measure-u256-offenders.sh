#!/usr/bin/env bash
# Record the four Step-1/Step-7 U256-plan offender measurements without
# overwriting an earlier run.  A TIMEOUT is measurement data here, not a
# wrapper failure; check.sh's classification is preserved in each report.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
FIXTURES="${ELEVM_FIXTURES:-$HOME/execution-specs/tests/fixtures/ethereum_tests/BlockchainTests}"

usage() {
  echo "usage: scripts/measure-u256-offenders.sh <label> [--no-build]" >&2
  echo "example: scripts/measure-u256-offenders.sh step1" >&2
  exit 2
}

[ $# -ge 1 ] && [ $# -le 2 ] || usage
LABEL="$1"
case "$LABEL" in
  *[!A-Za-z0-9._-]*|'')
    echo "label may contain only letters, digits, dot, underscore, and hyphen" >&2
    exit 2
    ;;
esac

NO_BUILD=0
if [ $# -eq 2 ]; then
  [ "$2" = "--no-build" ] || usage
  NO_BUILD=1
fi

OUT_DIR="${ELEVM_REPORT_DIR:-$SCRIPT_DIR}"
mkdir -p "$OUT_DIR"

run_measurement() {
  local name="$1"
  local path="$2"
  local build_flag="$3"
  local report="$OUT_DIR/report-$LABEL-$name.txt"
  local args=(--dir "$path" --report "$report")
  if [ "$build_flag" -eq 0 ]; then
    args+=(--no-build)
  fi

  echo "--- Measuring $name ---"
  "$SCRIPT_DIR/check.sh" "${args[@]}"
  local rc=$?
  if [ ! -s "$report" ]; then
    echo "RED — measurement did not produce $report" >&2
    return "$rc"
  fi
  echo "RECORDED — $report (check.sh exit $rc; TIMEOUT/FAIL classifications are retained for review)"
  return 0
}

BUILD_FIRST=$((1 - NO_BUILD))
run_measurement \
  vmPerformance \
  "$FIXTURES/GeneralStateTests/VMTests/vmPerformance" \
  "$BUILD_FIRST" || exit $?

run_measurement \
  CALLBlake2f_MaxRounds \
  "$FIXTURES/GeneralStateTests/stTimeConsuming/CALLBlake2f_MaxRounds.json" \
  0 || exit $?

run_measurement \
  static_Call50000_sha256 \
  "$FIXTURES/GeneralStateTests/stTimeConsuming/static_Call50000_sha256.json" \
  0 || exit $?

echo "OK — offender measurements recorded with label $LABEL"
