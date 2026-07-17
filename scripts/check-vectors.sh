#!/usr/bin/env bash

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(dirname "$SCRIPT_DIR")"
BIN="$ROOT/.lake/build/bin/elevm"

if [ ! -x "$BIN" ]; then
  echo "ERROR: elevm binary not found. Run 'lake build' first."
  exit 1
fi

REPORT="$SCRIPT_DIR/report-vectors.txt"
: > "$REPORT"

VECTORS_DIR="$SCRIPT_DIR/vectors"
CONTROL_FILES=(
  bn256Add.json
  bn256ScalarMul.json
  bn256Pairing.json
  blake2F.json
  modexp_eip2565.json
)

# Regenerate compact MSM samples from the pinned full files in
# scripts/vectors/SOURCES.md:
#   jq '.[0:32]' msm_G1_bls.json > scripts/vectors/msm_G1_bls.head.json
#   jq '.[0:32]' msm_G2_bls.json > scripts/vectors/msm_G2_bls.head.json
#   jq '.[0:32]' blsG1MultiExp.json > scripts/vectors/blsG1MultiExp.head.json
#   jq '.[0:32]' blsG2MultiExp.json > scripts/vectors/blsG2MultiExp.head.json

get_addr() {
  case "$1" in
    bn256Add.json) echo "06" ;;
    bn256ScalarMul.json) echo "07" ;;
    bn256Pairing.json) echo "08" ;;
    blake2F.json) echo "09" ;;
    modexp_eip2565.json) echo "05" ;;
    pointEvaluation.json) echo "0a" ;;
    add_G1_bls.json|fail-add_G1_bls.json|blsG1Add.json|fail-blsG1Add.json) echo "0b" ;;
    mul_G1_bls.json|fail-mul_G1_bls.json|msm_G1_bls.head.json|fail-msm_G1_bls.json|blsG1Mul.json|fail-blsG1Mul.json|blsG1MultiExp.head.json|fail-blsG1MultiExp.json) echo "0c" ;;
    add_G2_bls.json|fail-add_G2_bls.json|blsG2Add.json|fail-blsG2Add.json) echo "0d" ;;
    mul_G2_bls.json|fail-mul_G2_bls.json|msm_G2_bls.head.json|fail-msm_G2_bls.json|blsG2Mul.json|fail-blsG2Mul.json|blsG2MultiExp.head.json|fail-blsG2MultiExp.json) echo "0e" ;;
    pairing_check_bls.json|fail-pairing_check_bls.json|blsPairing.json|fail-blsPairing.json) echo "0f" ;;
    map_fp_to_G1_bls.json|fail-map_fp_to_G1_bls.json|blsMapG1.json|fail-blsMapG1.json) echo "10" ;;
    map_fp2_to_G2_bls.json|fail-map_fp2_to_G2_bls.json|blsMapG2.json|fail-blsMapG2.json) echo "11" ;;
    *) echo "" ;;
  esac
}

is_control_file() {
  local file="$1"
  local control
  for control in "${CONTROL_FILES[@]}"; do
    [ "$file" = "$control" ] && return 0
  done
  return 1
}

control_passes=0
unknown_files=0

run_vector_file() {
  local file="$1"
  local addr
  local path
  local runner_status
  local verdict
  local group

  addr="$(get_addr "$file")"
  path="$VECTORS_DIR/$file"
  if [ ! -f "$path" ]; then
    printf 'WARNING: missing vector file %s\n' "$file" | tee -a "$REPORT"
    unknown_files=$((unknown_files + 1))
    return
  fi
  if [ -z "$addr" ]; then
    printf 'WARNING: unknown address for %s\n' "$file" | tee -a "$REPORT"
    unknown_files=$((unknown_files + 1))
    return
  fi

  if is_control_file "$file"; then
    group="control"
  else
    group="BLS/point-eval"
  fi
  printf 'Running %s at address %s\n' "$file" "$addr" | tee -a "$REPORT"
  "$BIN" --vectors "$addr" "$path" | tee -a "$REPORT"
  runner_status=${PIPESTATUS[0]}
  if [ "$runner_status" -eq 0 ]; then
    verdict="OK"
  else
    verdict="RED"
  fi
  printf 'MATRIX\t%s\t%s\t%s\n' "$group" "$verdict" "$file" | tee -a "$REPORT"
  if [ "$group" = "control" ] && [ "$runner_status" -eq 0 ]; then
    control_passes=$((control_passes + 1))
  fi
}

printf '%s\n' '--- Running control files ---' | tee -a "$REPORT"
for file in "${CONTROL_FILES[@]}"; do
  run_vector_file "$file"
done

printf '%s\n' '--- Running BLS and point-evaluation files ---' | tee -a "$REPORT"
shopt -s nullglob
for path in "$VECTORS_DIR"/*.json; do
  file="$(basename "$path")"
  if is_control_file "$file"; then
    continue
  fi
  run_vector_file "$file"
done

control_total="${#CONTROL_FILES[@]}"
if [ "$control_passes" -eq "$control_total" ] && [ "$unknown_files" -eq 0 ]; then
  printf 'OK — vectors: controls %s/%s PASS; full matrix in %s\n' "$control_passes" "$control_total" "$REPORT"
  exit 0
fi
printf 'RED — vectors: controls %s/%s PASS, %s unknown files; target not met; see %s\n' \
  "$control_passes" "$control_total" "$unknown_files" "$REPORT"
exit 1
