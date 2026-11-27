#!/usr/bin/env python3
"""Compare the Python and Lean reconstructions of the certified DIMACS instance."""

import argparse
import hashlib
import json
from itertools import product, zip_longest
from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory

from encode_c4_polarity_42_cnf import orthogonal_permutations


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lrat", type=Path, help="check an LRAT trace on the Lean formula")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    script_dir = root / "scripts"
    points = [(1, a, b) for a, b in product(range(7), repeat=2)]
    points += [(0, 1, a) for a in range(7)] + [(0, 0, 1)]
    permutations = orthogonal_permutations(points)
    with TemporaryDirectory() as scratch:
        path = Path(scratch) / "permutations.json"
        path.write_text(json.dumps(permutations), encoding="ascii")
        command = [
            "lake", "env", "lean", "--run",
            str(script_dir / "emit_c4_polarity_42_lean.lean"), str(path),
        ]
        package = root / "conjectures" / "implications"
        numbered = subprocess.check_output(command, cwd=package)
        if args.lrat:
            subprocess.run([*command, str(args.lrat.resolve())], cwd=package, check=True)
    recursive = subprocess.check_output(
        [sys.executable, str(script_dir / "encode_c4_polarity_42_cnf.py"), "--symmetry"]
    )
    if numbered != recursive:
        for index, (lean, python) in enumerate(
            zip_longest(numbered.splitlines(), recursive.splitlines()), 1
        ):
            if lean != python:
                raise SystemExit(f"DIMACS line {index}: Lean={lean!r}, Python={python!r}")
        raise SystemExit("DIMACS files differ in line endings")
    digest = hashlib.sha256(numbered).hexdigest()
    expected = "27e22fc68ac0734d9e10c6a0e058345bd9aa10ce4e1824bbc18853d6947cd1ea"
    if digest != expected:
        raise SystemExit(f"DIMACS SHA-256 {digest} differs from the certified instance")
    print(f"{numbered.splitlines()[0].decode('ascii')} | SHA-256 {digest}")


if __name__ == "__main__":
    main()
