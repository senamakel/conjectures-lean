#!/usr/bin/env bash
# Link ERH for abelian fields to the riemann-hypothesis repository and print the axioms.
#
# Usage: scripts/check-unconditional.sh [RH_DIR]
#   RH_DIR defaults to ../riemann-hypothesis; it is cloned there if missing.
#   RH_REV pins the riemann-hypothesis commit (default: the one this was last checked against).
#
# Imports `Main` (for `LFunction_eq_zero_re : DirichletLZerosOnLine`), the module holding
# `UpperTheory.V.CF.kwHom` (Kronecker–Weber) and the Tate-thesis module
# `GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation` (a continuation of ζ_K, used only
# to show the ERH statement is not vacuous). The community cache contains outputs of untrusted
# builds: this links the proofs, it does not re-verify them. Set RH_FULL_BUILD=1 to rebuild the
# imported riemann-hypothesis modules from source instead (only Mathlib comes from its official
# cache).
set -euo pipefail

HERE="$(cd "$(dirname "$0")/.." && pwd)"
RH="${1:-$HERE/../riemann-hypothesis}"
RH_REV="${RH_REV:-507a75d91d}"
RH_MODULES="Main GroundTheory.GlobalFields.TateThesis.DedekindZetaContinuation Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.KwHom"

# Importing riemann-hypothesis modules opens many files.
ulimit -n "$(ulimit -Hn)" 2>/dev/null || true
if [ "$(ulimit -n)" != unlimited ] && [ "$(ulimit -n)" -lt 1000000 ]; then
  echo "warning: open-file limit is $(ulimit -n); the import may fail." >&2
  echo "  Linux: raise 'nofile' in /etc/security/limits.conf (and fs.file-max)" >&2
fi

if [ ! -d "$RH" ]; then
  git clone https://github.com/leanprover-community/riemann-hypothesis "$RH"
fi
if [ "$(git -C "$RH" rev-parse HEAD)" != "$(git -C "$RH" rev-parse "$RH_REV^{commit}" 2>/dev/null || echo none)" ]; then
  git -C "$RH" fetch -q origin
  git -C "$RH" checkout -q "$RH_REV"
fi

if [ "$(cat "$RH/lean-toolchain")" != "$(cat "$HERE/lean-toolchain")" ]; then
  echo "toolchain mismatch: $(cat "$RH/lean-toolchain") vs $(cat "$HERE/lean-toolchain")" >&2
  exit 1
fi

if [ "${RH_FULL_BUILD:-0}" = 1 ]; then
  (cd "$RH" && lake env true)   # materialize dependencies
  (cd "$RH/.lake/packages/mathlib" && lake exe cache get)
  rm -rf "$RH/.lake/build"
  (cd "$RH" && lake build $RH_MODULES)
else
  (cd "$RH" && lake exe cache get)
  (cd "$RH" && lake build --no-build $RH_MODULES)
fi

(cd "$HERE" && lake build)

cd "$HERE"
LEAN_PATH="$(cd "$RH" && lake env printenv LEAN_PATH):$HERE/.lake/packages/Erdos985/.lake/build/lib/lean:$HERE/.lake/packages/Artin/.lake/build/lib/lean:$HERE/.lake/build/lib/lean" \
  lean Unconditional/AbelianERHUnconditional.lean
