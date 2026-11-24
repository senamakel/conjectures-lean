#!/usr/bin/env bash
# Print the axioms of the headline theorems and fail unless each uses only the standard three.
# Usage: scripts/check-axioms.sh   (after `lake build`)
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d "${TMPDIR:-/tmp}/cramer-axioms.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import Cramer
#print axioms Cramer.primeInShortInterval_of_RH
#print axioms Cramer.primeGapExplicit_of_RH
#print axioms Cramer.cramer_of_RH
#print axioms Cramer.dyadicMeanSquare_of_RH
#print axioms Cramer.meanSquare_of_RH
#print axioms Cramer.logMeanSquare_of_RH
#print axioms Cramer.logMeanSquareAsymptotic_of_RH
LEAN
out="$(lake env lean "$tmp/Axioms.lean")"
echo "$out"
n="$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" <<<"$out" || true)"
if [ "$n" != 7 ]; then
  echo "axiom check FAILED: expected 7 theorems on the standard axioms only" >&2
  exit 1
fi
echo "axiom check passed"
