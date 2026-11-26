#!/usr/bin/env bash
set -euo pipefail
root=$(cd "$(dirname "$0")/.." && pwd)
work=$(mktemp -d "${TMPDIR:-/tmp}/bz-five-lock.XXXXXXXX")
trap 'rm -rf "$work"' EXIT
out="$root/verification-results"
mkdir -p "$out"
rm -f "$out"/{comparator.json,comparator.stderr,setup.log,status.txt,lake-manifest.json}
printf 'NOT VERIFIED: setup or verification incomplete\n' > "$out/status.txt"
exec > >(tee "$out/setup.log") 2>&1
cp "$root"/*.lean "$work/"
cp "$root/verification/Challenge.lean" "$work/FiveLockChallenge.lean"
cp "$root/verification/comparator.json" "$work/comparator.json"
cp "$root/lakefile.lean" "$work/lakefile.lean"
# Keep the original checkout and toolchain unchanged.
python3 - "$work/lakefile.lean" <<'PY'
import pathlib,sys
p=pathlib.Path(sys.argv[1]); s=p.read_text()
assert s.count('"v4.20.0"') == 1
s=s.replace('"v4.20.0"','"v4.35.0"')
# The challenge is a separate non-default library; do not import it into solution.
s+='\nlean_lib FiveLockChallenge\n'
p.write_text(s)
PY
printf 'leanprover/lean4:v4.35.0\n' > "$work/lean-toolchain"
cd "$work"
elan toolchain install leanprover/lean4:v4.35.0
# Use the actual toolchain binaries, not elan proxies inside the sandbox.
toolbin=$(dirname "$(elan which lean)")
export PATH="$toolbin:$PATH"
lean --version
lake update
cp lake-manifest.json "$out/lake-manifest.json"
# Comparator requires a clean project build. Remove generated artifacts and
# let Comparator resolve the pinned manifest again in its own sandbox.
rm -rf .lake
set +e
lake comparator --config=comparator.json --paranoid --json > "$out/comparator.json" 2> "$out/comparator.stderr"
rc=$?
set -e
cat "$out/comparator.stderr"
cat "$out/comparator.json"
if [[ $rc -eq 0 ]]; then
  printf 'VERIFIED: Comparator and all bundled kernels accepted the four endpoints\n' > "$out/status.txt"
else
  printf 'NOT VERIFIED: Comparator exit %s (1=rejected/build failure; 2=environment failure)\n' "$rc" > "$out/status.txt"
fi
cat "$out/status.txt"
exit "$rc"
