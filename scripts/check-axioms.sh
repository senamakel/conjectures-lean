#!/usr/bin/env bash
# Print the axioms of the headline theorems and fail unless each uses only the standard three.
# Usage: scripts/check-axioms.sh   (after `lake build`)
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d "${TMPDIR:-/tmp}/shoup-axioms.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import Shoup
#print axioms Shoup.ankenyType_of_GRH
#print axioms Shoup.leastPrimitiveRoot_le_of_GRH
#print axioms Shoup.prime_primitive_root_le_of_GRH
#print axioms Shoup.polyOmega_of_GRH
#print axioms Shoup.leastPrimitiveRoot_le_poly_of_GRH
#print axioms Shoup.polyOmega7_of_GRH
#print axioms Shoup.leastPrimitiveRoot_le_seven_of_GRH
LEAN
out="$(lake env lean "$tmp/Axioms.lean")"
echo "$out"
n="$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" <<<"$out" || true)"
if [ "$n" != 7 ]; then
  echo "axiom check FAILED: expected 7 theorems on the standard axioms only" >&2
  exit 1
fi
echo "axiom check passed"
