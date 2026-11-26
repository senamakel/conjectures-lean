#!/usr/bin/env bash
# Link the density-hypothesis proof to the riemann-hypothesis repository's RH theorem and print
# the axioms.
#
# Usage: scripts/check-unconditional.sh [RH_DIR]
#   RH_DIR defaults to ../riemann-hypothesis; it is cloned there if missing.
#   RH_REV pins the riemann-hypothesis commit (default: the one this was last checked against).
#
# An existing checkout that is already at RH_REV and already built is used read-only: nothing is
# fetched, checked out or rebuilt there.
#
# The community cache contains outputs of untrusted builds: this links the two proofs, it does
# not re-verify the RH proof. Set RH_FULL_BUILD=1 to rebuild every riemann-hypothesis module
# from source instead (only Mathlib comes from its official cache; many CPU hours).
set -euo pipefail

HERE="$(cd "$(dirname "$0")/.." && pwd)"
RH="${1:-$HERE/../riemann-hypothesis}"
RH_REV="${RH_REV:-507a75d91d}"

# The RH import opens ~900k module files.
ulimit -n "$(ulimit -Hn)" 2>/dev/null || true
if [ "$(ulimit -n)" != unlimited ] && [ "$(ulimit -n)" -lt 1000000 ]; then
  echo "warning: open-file limit is $(ulimit -n); the import may fail." >&2
  echo "  macOS: sudo sysctl -w kern.maxfiles=2000000 kern.maxfilesperproc=1500000 kern.maxvnodes=1500000" >&2
  echo "  Linux: raise 'nofile' in /etc/security/limits.conf (and fs.file-max)" >&2
fi

if [ ! -d "$RH" ]; then
  git clone https://github.com/leanprover-community/riemann-hypothesis "$RH"
fi
if [ "$(git -C "$RH" rev-parse HEAD)" != "$(git -C "$RH" rev-parse "$RH_REV^{commit}" 2>/dev/null)" ]; then
  git -C "$RH" fetch -q origin
  git -C "$RH" checkout -q "$RH_REV"
fi
echo "riemann-hypothesis at $(git -C "$RH" rev-parse HEAD)"

if [ "$(cat "$RH/lean-toolchain")" != "$(cat "$HERE/lean-toolchain")" ]; then
  echo "toolchain mismatch: $(cat "$RH/lean-toolchain") vs $(cat "$HERE/lean-toolchain")" >&2
  exit 1
fi

if [ "${RH_FULL_BUILD:-0}" = 1 ]; then
  # Only Mathlib comes from its official cache; every riemann-hypothesis module is rebuilt.
  (cd "$RH" && lake env true)   # materialize dependencies
  (cd "$RH/.lake/packages/mathlib" && lake exe cache get)
  rm -rf "$RH/.lake/build"
  (cd "$RH" && lake build Main)
elif ! (cd "$RH" && lake build --no-build Main >/dev/null 2>&1); then
  (cd "$RH" && lake exe cache get)
  (cd "$RH" && lake build --no-build Main)
fi

(cd "$HERE" && lake build)

cd "$HERE"
LEAN_PATH="$(cd "$RH" && lake env printenv LEAN_PATH):$HERE/../erdos-985/.lake/build/lib/lean:$HERE/.lake/build/lib/lean" \
  lean Unconditional/DensityUnconditional.lean
