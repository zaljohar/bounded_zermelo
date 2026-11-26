#!/usr/bin/env bash
set -euo pipefail

if [[ $# -gt 1 || ( $# -eq 1 && $1 != --docker ) ]]; then
  echo "Usage: $0 [--docker]" >&2
  exit 2
fi

root=$(cd "$(dirname "$0")/.." && pwd)
results="$root/verification-results"
mkdir -p "$results"
printf 'NOT VERIFIED. Setup or verification is incomplete.\n' > "$results/status.txt"
out=$(mktemp -d "$results/run.XXXXXXXX")
stage=$(mktemp -d "${TMPDIR:-/tmp}/bz-five-lock.XXXXXXXX")
trap 'rm -rf -- "$stage"' EXIT
exec > >(tee "$out/setup.log") 2>&1
printf 'Evidence directory: %s\n' "$out"

run_logged() {
  local name=$1 code=0
  shift
  printf 'Running %s\n' "$name"
  "$@" > "$out/$name.log" 2>&1 || code=$?
  printf '%s\n' "$code" > "$out/$name.exit"
  cat "$out/$name.log"
  return "$code"
}

cp "$root"/*.lean "$stage/"
cp "$root/verification/Challenge.lean" "$stage/FiveLockChallenge.lean"
cp "$root/verification/comparator.json" "$stage/comparator.json"
cp "$root/verification/lake-manifest.4.35.json" "$stage/lake-manifest.json"
cp "$stage/lake-manifest.json" "$out/lake-manifest.json"
printf 'leanprover/lean4:v4.35.0\n' > "$stage/lean-toolchain"
cd "$stage"
run_logged compatibility patch --batch --fuzz=0 -p1 -i "$root/verification/lean-4.35.patch"
run_logged install elan toolchain install leanprover/lean4:v4.35.0
toolbin=$(dirname "$(elan which lean)")
export PATH="$toolbin:$PATH"
export XDG_CACHE_HOME="$stage/cache"
run_logged version lean --version
run_logged resolve lake resolve-deps
mapfile -t mathlib_imports < <(awk '$1 == "import" && $2 ~ /^Mathlib\./ { print $2 }' ./*.lean | sort -u)
if ! run_logged cache lake exe cache get "${mathlib_imports[@]}"; then
  echo 'Mathlib cache unavailable. Lake will build the required dependencies from source.'
fi
run_logged build lake build FiveLockChallenge NineAxiomBZProof
run_logged audit lake env lean FoundationFreeKernelAudit.lean

if [[ $# -eq 1 ]]; then
  inputs="$stage/exports"
  mkdir "$inputs"
  cp "$stage/comparator.json" "$root/verification/check-exports.sh" "$inputs/"
  run_logged export bash "$root/verification/export.sh" "$inputs"
  cp "$inputs/"*.exit "$inputs/"*.stderr "$out/"
  (cd "$inputs" && sha256sum ./*.export) > "$out/export-sha256.txt"
  chmod a+rX "$inputs" "$inputs"/*
  run_logged docker-build docker build -t bz-checker-runtime "$root/verification"
  run_logged checks docker run --rm --network none --read-only --tmpfs /tmp \
    --cap-drop ALL --security-opt no-new-privileges \
    --mount "type=bind,src=$(dirname "$toolbin"),dst=/lean,readonly" \
    --mount "type=bind,src=$inputs,dst=/input,readonly" \
    --env PATH=/lean/bin:/usr/bin:/bin bz-checker-runtime bash /input/check-exports.sh
else
  run_logged checks lake comparator --config=comparator.json --paranoid
fi
printf 'VERIFIED. Comparator and all bundled kernels accepted all four endpoints.\n' \
  | tee "$results/status.txt"
