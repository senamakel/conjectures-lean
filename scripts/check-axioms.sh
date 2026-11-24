#!/usr/bin/env bash
# Print the axioms of the headline theorems and fail unless each uses only the standard three.
# Usage: scripts/check-axioms.sh   (after `lake build`)
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d "${TMPDIR:-/tmp}/erdos969-axioms.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import Erdos969
#print axioms Erdos969.squarefreeError_le
#print axioms Erdos969.axer_of_RH
#print axioms Erdos969.erdos_969_prime_number_theorem_of_RH
#print axioms Erdos969.KFree.kFreeError_le
#print axioms Erdos969.KFree.axerKFree_of_RH
#print axioms Erdos969.KFree.axerKFreeBound_two_iff
#print axioms Erdos969.MV.twisted_mertens
#print axioms Erdos969.MV.tail_le
#print axioms Erdos969.MV.abs_error_le_mv
#print axioms Erdos969.MV.montgomeryVaughan_of_RH
#print axioms Erdos969.MV.squarefreeError_mv_of_RH
LEAN
out="$(lake env lean "$tmp/Axioms.lean")"
echo "$out"
n="$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" <<<"$out" || true)"
if [ "$n" != 11 ]; then
  echo "axiom check FAILED: expected 11 theorems on the standard axioms only" >&2
  exit 1
fi
echo "axiom check passed"
