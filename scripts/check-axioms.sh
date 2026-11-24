#!/usr/bin/env bash
# Print the axioms of the headline theorems and fail unless each uses only the standard three.
# Usage: scripts/check-axioms.sh   (after `lake build`)
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d "${TMPDIR:-/tmp}/goldbach-average-axioms.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import GoldbachAverage
#print axioms GoldbachAverage.goldbachAverageSharp_of_RH
#print axioms GoldbachAverage.goldbachAverage_of_RH
LEAN
out="$(lake env lean "$tmp/Axioms.lean")"
echo "$out"
n="$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" <<<"$out" || true)"
if [ "$n" != 2 ]; then
  echo "axiom check FAILED: expected 2 theorems on the standard axioms only" >&2
  exit 1
fi
echo "axiom check passed"
