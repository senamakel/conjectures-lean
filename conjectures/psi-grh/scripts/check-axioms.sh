#!/usr/bin/env bash
# Print the axioms of the headline theorems and fail unless each uses only the standard three.
# Usage: scripts/check-axioms.sh   (after `lake build`)
set -euo pipefail
cd "$(dirname "$0")/.."
tmp="$(mktemp -d "${TMPDIR:-/tmp}/psigrh-axioms.XXXXXX")"
trap 'rm -rf "$tmp"' EXIT
cat > "$tmp/Axioms.lean" <<'LEAN'
import PsiGRH
#print axioms PsiGRH.psiChar_of_GRH
#print axioms PsiGRH.psiCharLogSq_of_GRH
#print axioms PsiGRH.psiAP_of_GRH
#print axioms PsiGRH.thetaAP_of_GRH
#print axioms PsiGRH.piAP_of_GRH
LEAN
out="$(lake env lean "$tmp/Axioms.lean")"
echo "$out"
n="$(grep -c "depends on axioms: \[propext, Classical.choice, Quot.sound\]$" <<<"$out" || true)"
if [ "$n" != 5 ]; then
  echo "axiom check FAILED: expected 5 theorems on the standard axioms only" >&2
  exit 1
fi
echo "axiom check passed"
