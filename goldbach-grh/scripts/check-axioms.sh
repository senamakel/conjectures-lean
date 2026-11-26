#!/usr/bin/env bash
# Print the axioms of the headline theorems and fail on anything outside the allow-list:
# propext, Classical.choice, Quot.sound and the `native_decide` axioms of the chunk lemmas
# `Goldbach.Check.{binary,ladder}_chunk_N`.
# Usage (after `lake build`): scripts/check-axioms.sh [OUT]
set -euo pipefail
HERE="$(cd "$(dirname "$0")/.." && pwd)"
OUT="${1:-/dev/stdout}"
cd "$HERE"
raw="$(lake env lean scripts/Axioms.lean)"
printf '%s\n' "$raw" > "$OUT"
bad="$(printf '%s\n' "$raw" | tr ',[]' '\n\n\n' | sed 's/^ *//; s/ *$//' | grep -v "depends on axioms" | grep -v '^$' \
  | grep -Ev '^(propext|Classical\.choice|Quot\.sound|Goldbach\.Check\.(binary|ladder)_chunk_[0-9]+\._native\.native_decide\.ax_[0-9_]+)$' || true)"
if [ -n "$bad" ]; then
  echo "unexpected axioms:" >&2; printf '%s\n' "$bad" >&2; exit 1
fi
printf '%s\n' "$raw" | awk '/depends on axioms/ {name=$1} {n[name]+=gsub(/native_decide\.ax/, "")} END {for (k in n) print k ": " n[k] " native_decide axioms"}' >&2
echo "axioms OK" >&2
