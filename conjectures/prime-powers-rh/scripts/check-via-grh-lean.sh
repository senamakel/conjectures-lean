#!/usr/bin/env bash
# Link the PrimePowers proofs to RH from conjectures/grh (the compact edition of lsernau/grh-lean,
# Apache-2.0, ported to this repository's Lean and Mathlib pin) and print the axioms.
#
# Usage: scripts/check-via-grh-lean.sh
#
# Everything is built from source here: conjectures/grh is built with `lake build` (one to two
# hours cold; see conjectures/grh/README.md), and only Mathlib comes from its official cache.
set -euo pipefail

HERE="$(cd "$(dirname "$0")/.." && pwd)"
GRH="$HERE/../grh"

if [ "$(cat "$GRH/lean-toolchain")" != "$(cat "$HERE/lean-toolchain")" ]; then
  echo "toolchain mismatch: $(cat "$GRH/lean-toolchain") vs $(cat "$HERE/lean-toolchain")" >&2
  exit 1
fi

(cd "$GRH" && lake build Main GRH)
(cd "$HERE" && lake build)

cd "$HERE"
LEAN_PATH="$(lake env printenv LEAN_PATH):$GRH/.lake/build/lib/lean" \
  lean Unconditional/PrimePowersViaGRHLean.lean
