#!/usr/bin/env bash
set -euo pipefail

if (( $# < 1 )); then
    printf 'usage: %s TRACE.lrat [LAKE_OPTIONS...]\n' "$0" >&2
    exit 2
fi

trace=$(realpath -- "$1")
shift
root=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)
cd -- "$root/conjectures/implications"
mkdir -p .lake
scratch=$(mktemp -d .lake/polarity-proof.XXXXXXXX)
trap 'rm -r -- "$scratch"' EXIT

# Lean's include_str accepts UTF-8. Preserve every byte in a separate code point.
python3 - "$trace" "$scratch/trace.utf8" <<'PY'
from pathlib import Path
import sys

Path(sys.argv[2]).write_bytes(Path(sys.argv[1]).read_bytes().decode("latin-1").encode("utf-8"))
PY
cp -- "$root/scripts/c4_polarity_42_embedded.lean" "$scratch/EmbeddedReplay.lean"

lake "$@" build Implications.C4PolarityFullAssignment Implications.C4PolaritySymmetryCertificate
lake "$@" env lean "$scratch/EmbeddedReplay.lean"
